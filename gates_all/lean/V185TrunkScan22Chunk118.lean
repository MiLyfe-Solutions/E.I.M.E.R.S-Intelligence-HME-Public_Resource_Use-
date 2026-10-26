import V185TrunkScan22Chunk117

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1056285 : List Nat := [1, 4, 2, 2, 1, 1, 1, 3, 1, 6]
def baseStart_1056285 : Nat := 118140960795 + 1056285 * 2 ^ 59
def prefixEnd_1056285 : Nat := 4983230072969 + 3 ^ 40 * 1056285 * 2
def baseEnd_1056285 : Nat := 361587942089670009186493

theorem tailTrace_1056285 : CollatzResearch.WordTrace tailWord_1056285 prefixEnd_1056285 361587942089670009186493 := by
  unfold tailWord_1056285
  simp only [CollatzResearch.WordTrace]
  refine ⟨38525878978267318960802309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25683919318844879307201539 38525878978267318960802309)
  ·
    refine ⟨7223602308425122305150433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38525878978267318960802309 7223602308425122305150433)
    ·
      refine ⟨5417701731318841728862825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7223602308425122305150433 5417701731318841728862825)
      ·
        refine ⟨4063276298489131296647119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5417701731318841728862825 4063276298489131296647119)
        ·
          refine ⟨6094914447733696944970679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4063276298489131296647119 6094914447733696944970679)
          ·
            refine ⟨9142371671600545417456019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6094914447733696944970679 9142371671600545417456019)
            ·
              refine ⟨13713557507400818126184029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9142371671600545417456019 13713557507400818126184029)
              ·
                refine ⟨5142584065275306797319011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13713557507400818126184029 5142584065275306797319011)
                ·
                  refine ⟨7713876097912960195978517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5142584065275306797319011 7713876097912960195978517)
                  ·
                    refine ⟨361587942089670009186493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7713876097912960195978517 361587942089670009186493)
                    ·
                      rfl

theorem cell22_1056285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_1056285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1056285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1056285 prefixEnd_1056285 := by exact prefixLift 1056285
  have htrace : WordTrace (prefixWord ++ tailWord_1056285) baseStart_1056285 baseEnd_1056285 := by
    simpa [prefixWord, tailWord_1056285, baseEnd_1056285] using wordTrace_append hprefix tailTrace_1056285
  have hstable : (prefixWord ++ tailWord_1056285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056285).length < 2 ^ (prefixWord ++ tailWord_1056285).sum := by decide
  have hdescent : baseEnd_1056285 < baseStart_1056285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056289 : List Nat := [1, 2, 3, 2, 2, 4, 1, 3, 4]
def baseStart_1056289 : Nat := 118140960795 + 1056289 * 2 ^ 59
def prefixEnd_1056289 : Nat := 4983230072969 + 3 ^ 40 * 1056289 * 2
def baseEnd_1056289 : Nat := 120529770457138444028827

theorem tailTrace_1056289 : CollatzResearch.WordTrace tailWord_1056289 prefixEnd_1056289 120529770457138444028827 := by
  unfold tailWord_1056289
  simp only [CollatzResearch.WordTrace]
  refine ⟨38526024870252827643947921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25684016580168551762631947 38526024870252827643947921)
  ·
    refine ⟨28894518652689620732960941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38526024870252827643947921 28894518652689620732960941)
    ·
      refine ⟨10835444494758607774860353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28894518652689620732960941 10835444494758607774860353)
      ·
        refine ⟨8126583371068955831145265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10835444494758607774860353 8126583371068955831145265)
        ·
          refine ⟨6094937528301716873358949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8126583371068955831145265 6094937528301716873358949)
          ·
            refine ⟨1142800786556571913754803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6094937528301716873358949 1142800786556571913754803)
            ·
              refine ⟨1714201179834857870632205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1142800786556571913754803 1714201179834857870632205)
              ·
                refine ⟨642825442438071701487077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1714201179834857870632205 642825442438071701487077)
                ·
                  refine ⟨120529770457138444028827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 642825442438071701487077 120529770457138444028827)
                  ·
                    rfl

theorem cell22_1056289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 3, 4].length) (baseStart_1056289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1056289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1056289 prefixEnd_1056289 := by exact prefixLift 1056289
  have htrace : WordTrace (prefixWord ++ tailWord_1056289) baseStart_1056289 baseEnd_1056289 := by
    simpa [prefixWord, tailWord_1056289, baseEnd_1056289] using wordTrace_append hprefix tailTrace_1056289
  have hstable : (prefixWord ++ tailWord_1056289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056289).length < 2 ^ (prefixWord ++ tailWord_1056289).sum := by decide
  have hdescent : baseEnd_1056289 < baseStart_1056289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056302 : List Nat := [4, 1, 3, 1, 2, 1, 1, 1, 4, 4]
def baseStart_1056302 : Nat := 118140960795 + 1056302 * 2 ^ 59
def prefixEnd_1056302 : Nat := 4983230072969 + 3 ^ 40 * 1056302 * 2
def baseEnd_1056302 : Nat := 361593761537087631511441

theorem tailTrace_1056302 : CollatzResearch.WordTrace tailWord_1056302 prefixEnd_1056302 361593761537087631511441 := by
  unfold tailWord_1056302
  simp only [CollatzResearch.WordTrace]
  refine ⟨4815812377400716358021395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25684332679470487242780773 4815812377400716358021395)
  ·
    refine ⟨7223718566101074537032093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4815812377400716358021395 7223718566101074537032093)
    ·
      refine ⟨2708894462287902951387035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7223718566101074537032093 2708894462287902951387035)
      ·
        refine ⟨4063341693431854427080553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2708894462287902951387035 4063341693431854427080553)
        ·
          refine ⟨3047506270073890820310415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4063341693431854427080553 3047506270073890820310415)
          ·
            refine ⟨4571259405110836230465623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3047506270073890820310415 4571259405110836230465623)
            ·
              refine ⟨6856889107666254345698435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4571259405110836230465623 6856889107666254345698435)
              ·
                refine ⟨10285333661499381518547653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6856889107666254345698435 10285333661499381518547653)
                ·
                  refine ⟨1928500061531134034727685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10285333661499381518547653 1928500061531134034727685)
                  ·
                    refine ⟨361593761537087631511441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1928500061531134034727685 361593761537087631511441)
                    ·
                      rfl

theorem cell22_1056302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_1056302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1056302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1056302 prefixEnd_1056302 := by exact prefixLift 1056302
  have htrace : WordTrace (prefixWord ++ tailWord_1056302) baseStart_1056302 baseEnd_1056302 := by
    simpa [prefixWord, tailWord_1056302, baseEnd_1056302] using wordTrace_append hprefix tailTrace_1056302
  have hstable : (prefixWord ++ tailWord_1056302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056302).length < 2 ^ (prefixWord ++ tailWord_1056302).sum := by decide
  have hdescent : baseEnd_1056302 < baseStart_1056302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056317 : List Nat := [1, 4, 1, 3, 3, 1, 2, 7]
def baseStart_1056317 : Nat := 118140960795 + 1056317 * 2 ^ 59
def prefixEnd_1056317 : Nat := 4983230072969 + 3 ^ 40 * 1056317 * 2
def baseEnd_1056317 : Nat := 40177655149292510265155

theorem tailTrace_1056317 : CollatzResearch.WordTrace tailWord_1056317 prefixEnd_1056317 40177655149292510265155 := by
  unfold tailWord_1056317
  simp only [CollatzResearch.WordTrace]
  refine ⟨38527046114151388425967205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25684697409434258950644803 38527046114151388425967205)
  ·
    refine ⟨7223821146403385329868851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38527046114151388425967205 7223821146403385329868851)
    ·
      refine ⟨10835731719605077994803277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7223821146403385329868851 10835731719605077994803277)
      ·
        refine ⟨4063399394851904248051229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10835731719605077994803277 4063399394851904248051229)
        ·
          refine ⟨1523774773069464093019211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4063399394851904248051229 1523774773069464093019211)
          ·
            refine ⟨2285662159604196139528817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1523774773069464093019211 2285662159604196139528817)
            ·
              refine ⟨1714246619703147104646613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2285662159604196139528817 1714246619703147104646613)
              ·
                refine ⟨40177655149292510265155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1714246619703147104646613 40177655149292510265155)
                ·
                  rfl

theorem cell22_1056317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 7].length) (baseStart_1056317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1056317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1056317 prefixEnd_1056317 := by exact prefixLift 1056317
  have htrace : WordTrace (prefixWord ++ tailWord_1056317) baseStart_1056317 baseEnd_1056317 := by
    simpa [prefixWord, tailWord_1056317, baseEnd_1056317] using wordTrace_append hprefix tailTrace_1056317
  have hstable : (prefixWord ++ tailWord_1056317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056317).length < 2 ^ (prefixWord ++ tailWord_1056317).sum := by decide
  have hdescent : baseEnd_1056317 < baseStart_1056317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056362 : List Nat := [3, 1, 3, 2, 1, 2, 1, 4, 5]
def baseStart_1056362 : Nat := 118140960795 + 1056362 * 2 ^ 59
def prefixEnd_1056362 : Nat := 4983230072969 + 3 ^ 40 * 1056362 * 2
def baseEnd_1056362 : Nat := 120538100254422491670419

theorem tailTrace_1056362 : CollatzResearch.WordTrace tailWord_1056362 prefixEnd_1056362 120538100254422491670419 := by
  unfold tailWord_1056362
  simp only [CollatzResearch.WordTrace]
  refine ⟨9632171849747090277838835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25685791599325574074236893 9632171849747090277838835)
  ·
    refine ⟨14448257774620635416758253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9632171849747090277838835 14448257774620635416758253)
    ·
      refine ⟨5418096665482738281284345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14448257774620635416758253 5418096665482738281284345)
      ·
        refine ⟨4063572499112053710963259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5418096665482738281284345 4063572499112053710963259)
        ·
          refine ⟨6095358748668080566444889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4063572499112053710963259 6095358748668080566444889)
          ·
            refine ⟨4571519061501060424833667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6095358748668080566444889 4571519061501060424833667)
            ·
              refine ⟨6857278592251590637250501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4571519061501060424833667 6857278592251590637250501)
              ·
                refine ⟨1285739736047173244484469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6857278592251590637250501 1285739736047173244484469)
                ·
                  refine ⟨120538100254422491670419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1285739736047173244484469 120538100254422491670419)
                  ·
                    rfl

theorem cell22_1056362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 4, 5].length) (baseStart_1056362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1056362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1056362 prefixEnd_1056362 := by exact prefixLift 1056362
  have htrace : WordTrace (prefixWord ++ tailWord_1056362) baseStart_1056362 baseEnd_1056362 := by
    simpa [prefixWord, tailWord_1056362, baseEnd_1056362] using wordTrace_append hprefix tailTrace_1056362
  have hstable : (prefixWord ++ tailWord_1056362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056362).length < 2 ^ (prefixWord ++ tailWord_1056362).sum := by decide
  have hdescent : baseEnd_1056362 < baseStart_1056362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056435 : List Nat := [1, 1, 1, 2, 3, 3, 2, 9]
def baseStart_1056435 : Nat := 118140960795 + 1056435 * 2 ^ 59
def prefixEnd_1056435 : Nat := 4983230072969 + 3 ^ 40 * 1056435 * 2
def baseEnd_1056435 : Nat := 40182143350568846437337

theorem tailTrace_1056435 : CollatzResearch.WordTrace tailWord_1056435 prefixEnd_1056435 40182143350568846437337 := by
  unfold tailWord_1056435
  simp only [CollatzResearch.WordTrace]
  refine ⟨38531349927723894578762759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25687566618482596385841839 38531349927723894578762759)
  ·
    refine ⟨57797024891585841868144139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38531349927723894578762759 57797024891585841868144139)
    ·
      refine ⟨86695537337378762802216209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57797024891585841868144139 86695537337378762802216209)
      ·
        refine ⟨65021653003034072101662157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86695537337378762802216209 65021653003034072101662157)
        ·
          refine ⟨24383119876137777038123309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65021653003034072101662157 24383119876137777038123309)
          ·
            refine ⟨9143669953551666389296241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24383119876137777038123309 9143669953551666389296241)
            ·
              refine ⟨6857752465163749791972181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9143669953551666389296241 6857752465163749791972181)
              ·
                refine ⟨40182143350568846437337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6857752465163749791972181 40182143350568846437337)
                ·
                  rfl

theorem cell22_1056435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 9].length) (baseStart_1056435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1056435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1056435 prefixEnd_1056435 := by exact prefixLift 1056435
  have htrace : WordTrace (prefixWord ++ tailWord_1056435) baseStart_1056435 baseEnd_1056435 := by
    simpa [prefixWord, tailWord_1056435, baseEnd_1056435] using wordTrace_append hprefix tailTrace_1056435
  have hstable : (prefixWord ++ tailWord_1056435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056435).length < 2 ^ (prefixWord ++ tailWord_1056435).sum := by decide
  have hdescent : baseEnd_1056435 < baseStart_1056435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056439 : List Nat := [1, 1, 3, 1, 5, 3, 1, 1, 1, 5]
def baseStart_1056439 : Nat := 118140960795 + 1056439 * 2 ^ 59
def prefixEnd_1056439 : Nat := 4983230072969 + 3 ^ 40 * 1056439 * 2
def baseEnd_1056439 : Nat := 361640659436864940836021

theorem tailTrace_1056439 : CollatzResearch.WordTrace tailWord_1056439 prefixEnd_1056439 361640659436864940836021 := by
  unfold tailWord_1056439
  simp only [CollatzResearch.WordTrace]
  refine ⟨38531495819709403261908371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25687663879806268841272247 38531495819709403261908371)
  ·
    refine ⟨57797243729564104892862557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38531495819709403261908371 57797243729564104892862557)
    ·
      refine ⟨21673966398586539334823459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57797243729564104892862557 21673966398586539334823459)
      ·
        refine ⟨32510949597879809002235189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21673966398586539334823459 32510949597879809002235189)
        ·
          refine ⟨3047901524801232093959549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32510949597879809002235189 3047901524801232093959549)
          ·
            refine ⟨1142963071800462035234831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3047901524801232093959549 1142963071800462035234831)
            ·
              refine ⟨1714444607700693052852247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1142963071800462035234831 1714444607700693052852247)
              ·
                refine ⟨2571666911551039579278371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1714444607700693052852247 2571666911551039579278371)
                ·
                  refine ⟨3857500367326559368917557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2571666911551039579278371 3857500367326559368917557)
                  ·
                    refine ⟨361640659436864940836021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3857500367326559368917557 361640659436864940836021)
                    ·
                      rfl

theorem cell22_1056439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 5].length) (baseStart_1056439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1056439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1056439 prefixEnd_1056439 := by exact prefixLift 1056439
  have htrace : WordTrace (prefixWord ++ tailWord_1056439) baseStart_1056439 baseEnd_1056439 := by
    simpa [prefixWord, tailWord_1056439, baseEnd_1056439] using wordTrace_append hprefix tailTrace_1056439
  have hstable : (prefixWord ++ tailWord_1056439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056439).length < 2 ^ (prefixWord ++ tailWord_1056439).sum := by decide
  have hdescent : baseEnd_1056439 < baseStart_1056439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056452 : List Nat := [2, 3, 3, 1, 1, 1, 3, 8]
def baseStart_1056452 : Nat := 118140960795 + 1056452 * 2 ^ 59
def prefixEnd_1056452 : Nat := 4983230072969 + 3 ^ 40 * 1056452 * 2
def baseEnd_1056452 : Nat := 40182789955837471140109

theorem tailTrace_1056452 : CollatzResearch.WordTrace tailWord_1056452 prefixEnd_1056452 40182789955837471140109 := by
  unfold tailWord_1056452
  simp only [CollatzResearch.WordTrace]
  refine ⟨19265984984331153241065805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25687979979108204321421073 19265984984331153241065805)
  ·
    refine ⟨7224744369124182465399677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19265984984331153241065805 7224744369124182465399677)
    ·
      refine ⟨2709279138421568424524879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7224744369124182465399677 2709279138421568424524879)
      ·
        refine ⟨4063918707632352636787319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2709279138421568424524879 4063918707632352636787319)
        ·
          refine ⟨6095878061448528955180979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4063918707632352636787319 6095878061448528955180979)
          ·
            refine ⟨9143817092172793432771469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6095878061448528955180979 9143817092172793432771469)
            ·
              refine ⟨3428931409564797537289301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9143817092172793432771469 3428931409564797537289301)
              ·
                refine ⟨40182789955837471140109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3428931409564797537289301 40182789955837471140109)
                ·
                  rfl

theorem cell22_1056452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 8].length) (baseStart_1056452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1056452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1056452 prefixEnd_1056452 := by exact prefixLift 1056452
  have htrace : WordTrace (prefixWord ++ tailWord_1056452) baseStart_1056452 baseEnd_1056452 := by
    simpa [prefixWord, tailWord_1056452, baseEnd_1056452] using wordTrace_append hprefix tailTrace_1056452
  have hstable : (prefixWord ++ tailWord_1056452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056452).length < 2 ^ (prefixWord ++ tailWord_1056452).sum := by decide
  have hdescent : baseEnd_1056452 < baseStart_1056452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056458 : List Nat := [3, 1, 2, 1, 6, 1, 1, 3, 4]
def baseStart_1056458 : Nat := 118140960795 + 1056458 * 2 ^ 59
def prefixEnd_1056458 : Nat := 4983230072969 + 3 ^ 40 * 1056458 * 2
def baseEnd_1056458 : Nat := 120549054508385074870321

theorem tailTrace_1056458 : CollatzResearch.WordTrace tailWord_1056458 prefixEnd_1056458 120549054508385074870321 := by
  unfold tailWord_1056458
  simp only [CollatzResearch.WordTrace]
  refine ⟨9633047201660142376712507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25688125871093713004566685 9633047201660142376712507)
  ·
    refine ⟨14449570802490213565068761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9633047201660142376712507 14449570802490213565068761)
    ·
      refine ⟨10837178101867660173801571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14449570802490213565068761 10837178101867660173801571)
      ·
        refine ⟨16255767152801490260702357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10837178101867660173801571 16255767152801490260702357)
        ·
          refine ⟨761989085287569855970423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16255767152801490260702357 761989085287569855970423)
          ·
            refine ⟨1142983627931354783955635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 761989085287569855970423 1142983627931354783955635)
            ·
              refine ⟨1714475441897032175933453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1142983627931354783955635 1714475441897032175933453)
              ·
                refine ⟨642928290711387065975045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1714475441897032175933453 642928290711387065975045)
                ·
                  refine ⟨120549054508385074870321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 642928290711387065975045 120549054508385074870321)
                  ·
                    rfl

theorem cell22_1056458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 3, 4].length) (baseStart_1056458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1056458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1056458 prefixEnd_1056458 := by exact prefixLift 1056458
  have htrace : WordTrace (prefixWord ++ tailWord_1056458) baseStart_1056458 baseEnd_1056458 := by
    simpa [prefixWord, tailWord_1056458, baseEnd_1056458] using wordTrace_append hprefix tailTrace_1056458
  have hstable : (prefixWord ++ tailWord_1056458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056458).length < 2 ^ (prefixWord ++ tailWord_1056458).sum := by decide
  have hdescent : baseEnd_1056458 < baseStart_1056458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056535 : List Nat := [1, 1, 3, 4, 2, 3, 2, 2, 1, 3]
def baseStart_1056535 : Nat := 118140960795 + 1056535 * 2 ^ 59
def prefixEnd_1056535 : Nat := 4983230072969 + 3 ^ 40 * 1056535 * 2
def baseEnd_1056535 : Nat := 361673522198752690435727

theorem tailTrace_1056535 : CollatzResearch.WordTrace tailWord_1056535 prefixEnd_1056535 361673522198752690435727 := by
  unfold tailWord_1056535
  simp only [CollatzResearch.WordTrace]
  refine ⟨38534997227361611657403059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25689998151574407771602039 38534997227361611657403059)
  ·
    refine ⟨57802495841042417486104589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38534997227361611657403059 57802495841042417486104589)
    ·
      refine ⟨21675935940390906557289221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57802495841042417486104589 21675935940390906557289221)
      ·
        refine ⟨4064237988823294979491729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21675935940390906557289221 4064237988823294979491729)
        ·
          refine ⟨3048178491617471234618797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4064237988823294979491729 3048178491617471234618797)
          ·
            refine ⟨1143066934356551712982049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3048178491617471234618797 1143066934356551712982049)
            ·
              refine ⟨857300200767413784736537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1143066934356551712982049 857300200767413784736537)
              ·
                refine ⟨642975150575560338552403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 857300200767413784736537 642975150575560338552403)
                ·
                  refine ⟨964462725863340507828605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 642975150575560338552403 964462725863340507828605)
                  ·
                    refine ⟨361673522198752690435727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 964462725863340507828605 361673522198752690435727)
                    ·
                      rfl

theorem cell22_1056535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 2, 1, 3].length) (baseStart_1056535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1056535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1056535 prefixEnd_1056535 := by exact prefixLift 1056535
  have htrace : WordTrace (prefixWord ++ tailWord_1056535) baseStart_1056535 baseEnd_1056535 := by
    simpa [prefixWord, tailWord_1056535, baseEnd_1056535] using wordTrace_append hprefix tailTrace_1056535
  have hstable : (prefixWord ++ tailWord_1056535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056535).length < 2 ^ (prefixWord ++ tailWord_1056535).sum := by decide
  have hdescent : baseEnd_1056535 < baseStart_1056535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056608 : List Nat := [2, 1, 1, 3, 3, 3, 3, 1, 2, 3]
def baseStart_1056608 : Nat := 118140960795 + 1056608 * 2 ^ 59
def prefixEnd_1056608 : Nat := 4983230072969 + 3 ^ 40 * 1056608 * 2
def baseEnd_1056608 : Nat := 361698511590604833360503

theorem tailTrace_1056608 : CollatzResearch.WordTrace tailWord_1056608 prefixEnd_1056608 361698511590604833360503 := by
  unfold tailWord_1056608
  simp only [CollatzResearch.WordTrace]
  refine ⟨19268829878048572562405239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25691773170731430083206985 19268829878048572562405239)
  ·
    refine ⟨28903244817072858843607859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19268829878048572562405239 28903244817072858843607859)
    ·
      refine ⟨43354867225609288265411789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28903244817072858843607859 43354867225609288265411789)
      ·
        refine ⟨16258075209603483099529421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43354867225609288265411789 16258075209603483099529421)
        ·
          refine ⟨6096778203601306162323533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16258075209603483099529421 6096778203601306162323533)
          ·
            refine ⟨2286291826350489810871325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6096778203601306162323533 2286291826350489810871325)
            ·
              refine ⟨857359434881433679076747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2286291826350489810871325 857359434881433679076747)
              ·
                refine ⟨1286039152322150518615121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 857359434881433679076747 1286039152322150518615121)
                ·
                  refine ⟨964529364241612888961341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1286039152322150518615121 964529364241612888961341)
                  ·
                    refine ⟨361698511590604833360503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 964529364241612888961341 361698511590604833360503)
                    ·
                      rfl

theorem cell22_1056608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 1, 2, 3].length) (baseStart_1056608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1056608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1056608 prefixEnd_1056608 := by exact prefixLift 1056608
  have htrace : WordTrace (prefixWord ++ tailWord_1056608) baseStart_1056608 baseEnd_1056608 := by
    simpa [prefixWord, tailWord_1056608, baseEnd_1056608] using wordTrace_append hprefix tailTrace_1056608
  have hstable : (prefixWord ++ tailWord_1056608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056608).length < 2 ^ (prefixWord ++ tailWord_1056608).sum := by decide
  have hdescent : baseEnd_1056608 < baseStart_1056608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056617 : List Nat := [1, 2, 1, 1, 1, 3, 1, 4, 2, 6]
def baseStart_1056617 : Nat := 118140960795 + 1056617 * 2 ^ 59
def prefixEnd_1056617 : Nat := 4983230072969 + 3 ^ 40 * 1056617 * 2
def baseEnd_1056617 : Nat := 361701592474531809885475

theorem tailTrace_1056617 : CollatzResearch.WordTrace tailWord_1056617 prefixEnd_1056617 361701592474531809885475 := by
  unfold tailWord_1056617
  simp only [CollatzResearch.WordTrace]
  refine ⟨38537988013064539661888105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25691992008709693107925403 38537988013064539661888105)
  ·
    refine ⟨28903491009798404746416079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38537988013064539661888105 28903491009798404746416079)
    ·
      refine ⟨43355236514697607119624119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28903491009798404746416079 43355236514697607119624119)
      ·
        refine ⟨65032854772046410679436179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43355236514697607119624119 65032854772046410679436179)
        ·
          refine ⟨97549282158069616019154269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65032854772046410679436179 97549282158069616019154269)
          ·
            refine ⟨36580980809276106007182851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97549282158069616019154269 36580980809276106007182851)
            ·
              refine ⟨54871471213914159010774277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36580980809276106007182851 54871471213914159010774277)
              ·
                refine ⟨10288400852608904814520177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54871471213914159010774277 10288400852608904814520177)
                ·
                  refine ⟨7716300639456678610890133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10288400852608904814520177 7716300639456678610890133)
                  ·
                    refine ⟨361701592474531809885475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7716300639456678610890133 361701592474531809885475)
                    ·
                      rfl

theorem cell22_1056617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 6].length) (baseStart_1056617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1056617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1056617 prefixEnd_1056617 := by exact prefixLift 1056617
  have htrace : WordTrace (prefixWord ++ tailWord_1056617) baseStart_1056617 baseEnd_1056617 := by
    simpa [prefixWord, tailWord_1056617, baseEnd_1056617] using wordTrace_append hprefix tailTrace_1056617
  have hstable : (prefixWord ++ tailWord_1056617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056617).length < 2 ^ (prefixWord ++ tailWord_1056617).sum := by decide
  have hdescent : baseEnd_1056617 < baseStart_1056617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056649 : List Nat := [1, 2, 1, 1, 5, 1, 2, 4, 5]
def baseStart_1056649 : Nat := 118140960795 + 1056649 * 2 ^ 59
def prefixEnd_1056649 : Nat := 4983230072969 + 3 ^ 40 * 1056649 * 2
def baseEnd_1056649 : Nat := 120570848909498131028459

theorem tailTrace_1056649 : CollatzResearch.WordTrace tailWord_1056649 prefixEnd_1056649 120570848909498131028459 := by
  unfold tailWord_1056649
  simp only [CollatzResearch.WordTrace]
  refine ⟨38539155148948609127053001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25692770099299072751368667 38539155148948609127053001)
  ·
    refine ⟨28904366361711456845289751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38539155148948609127053001 28904366361711456845289751)
    ·
      refine ⟨43356549542567185267934627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28904366361711456845289751 43356549542567185267934627)
      ·
        refine ⟨65034824313850777901901941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43356549542567185267934627 65034824313850777901901941)
        ·
          refine ⟨6097014779423510428303307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65034824313850777901901941 6097014779423510428303307)
          ·
            refine ⟨9145522169135265642454961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6097014779423510428303307 9145522169135265642454961)
            ·
              refine ⟨6859141626851449231841221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9145522169135265642454961 6859141626851449231841221)
              ·
                refine ⟨1286089055034646730970229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6859141626851449231841221 1286089055034646730970229)
                ·
                  refine ⟨120570848909498131028459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1286089055034646730970229 120570848909498131028459)
                  ·
                    rfl

theorem cell22_1056649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 4, 5].length) (baseStart_1056649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1056649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1056649 prefixEnd_1056649 := by exact prefixLift 1056649
  have htrace : WordTrace (prefixWord ++ tailWord_1056649) baseStart_1056649 baseEnd_1056649 := by
    simpa [prefixWord, tailWord_1056649, baseEnd_1056649] using wordTrace_append hprefix tailTrace_1056649
  have hstable : (prefixWord ++ tailWord_1056649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056649).length < 2 ^ (prefixWord ++ tailWord_1056649).sum := by decide
  have hdescent : baseEnd_1056649 < baseStart_1056649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056666 : List Nat := [3, 1, 1, 4, 2, 2, 1, 3, 5]
def baseStart_1056666 : Nat := 118140960795 + 1056666 * 2 ^ 59
def prefixEnd_1056666 : Nat := 4983230072969 + 3 ^ 40 * 1056666 * 2
def baseEnd_1056666 : Nat := 120572788725304005136775

theorem tailTrace_1056666 : CollatzResearch.WordTrace tailWord_1056666 prefixEnd_1056666 120572788725304005136775 := by
  unfold tailWord_1056666
  simp only [CollatzResearch.WordTrace]
  refine ⟨9634943797471755257605463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25693183459924680686947901 9634943797471755257605463)
  ·
    refine ⟨14452415696207632886408195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9634943797471755257605463 14452415696207632886408195)
    ·
      refine ⟨21678623544311449329612293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14452415696207632886408195 21678623544311449329612293)
      ·
        refine ⟨4064741914558396749302305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21678623544311449329612293 4064741914558396749302305)
        ·
          refine ⟨3048556435918797561976729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4064741914558396749302305 3048556435918797561976729)
          ·
            refine ⟨2286417326939098171482547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3048556435918797561976729 2286417326939098171482547)
            ·
              refine ⟨3429625990408647257223821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2286417326939098171482547 3429625990408647257223821)
              ·
                refine ⟨1286109746403242721458933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3429625990408647257223821 1286109746403242721458933)
                ·
                  refine ⟨120572788725304005136775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1286109746403242721458933 120572788725304005136775)
                  ·
                    rfl

theorem cell22_1056666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 3, 5].length) (baseStart_1056666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1056666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1056666 prefixEnd_1056666 := by exact prefixLift 1056666
  have htrace : WordTrace (prefixWord ++ tailWord_1056666) baseStart_1056666 baseEnd_1056666 := by
    simpa [prefixWord, tailWord_1056666, baseEnd_1056666] using wordTrace_append hprefix tailTrace_1056666
  have hstable : (prefixWord ++ tailWord_1056666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056666).length < 2 ^ (prefixWord ++ tailWord_1056666).sum := by decide
  have hdescent : baseEnd_1056666 < baseStart_1056666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056805 : List Nat := [1, 3, 1, 2, 2, 3, 3, 3, 1, 3]
def baseStart_1056805 : Nat := 118140960795 + 1056805 * 2 ^ 59
def prefixEnd_1056805 : Nat := 4983230072969 + 3 ^ 40 * 1056805 * 2
def baseEnd_1056805 : Nat := 361765948716561986184899

theorem tailTrace_1056805 : CollatzResearch.WordTrace tailWord_1056805 prefixEnd_1056805 361765948716561986184899 := by
  unfold tailWord_1056805
  simp only [CollatzResearch.WordTrace]
  refine ⟨38544844936383447769731869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25696563290922298513154579 38544844936383447769731869)
  ·
    refine ⟨14454316851143792913649451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38544844936383447769731869 14454316851143792913649451)
    ·
      refine ⟨21681475276715689370474177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14454316851143792913649451 21681475276715689370474177)
      ·
        refine ⟨16261106457536767027855633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21681475276715689370474177 16261106457536767027855633)
        ·
          refine ⟨12195829843152575270891725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16261106457536767027855633 12195829843152575270891725)
          ·
            refine ⟨4573436191182215726584397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12195829843152575270891725 4573436191182215726584397)
            ·
              refine ⟨1715038571693330897469149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4573436191182215726584397 1715038571693330897469149)
              ·
                refine ⟨643139464384999086550931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1715038571693330897469149 643139464384999086550931)
                ·
                  refine ⟨964709196577498629826397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 643139464384999086550931 964709196577498629826397)
                  ·
                    refine ⟨361765948716561986184899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 964709196577498629826397 361765948716561986184899)
                    ·
                      rfl

theorem cell22_1056805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 3, 1, 3].length) (baseStart_1056805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1056805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1056805 prefixEnd_1056805 := by exact prefixLift 1056805
  have htrace : WordTrace (prefixWord ++ tailWord_1056805) baseStart_1056805 baseEnd_1056805 := by
    simpa [prefixWord, tailWord_1056805, baseEnd_1056805] using wordTrace_append hprefix tailTrace_1056805
  have hstable : (prefixWord ++ tailWord_1056805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056805).length < 2 ^ (prefixWord ++ tailWord_1056805).sum := by decide
  have hdescent : baseEnd_1056805 < baseStart_1056805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056880 : List Nat := [2, 1, 1, 1, 5, 2, 4, 2, 4]
def baseStart_1056880 : Nat := 118140960795 + 1056880 * 2 ^ 59
def prefixEnd_1056880 : Nat := 4983230072969 + 3 ^ 40 * 1056880 * 2
def baseEnd_1056880 : Nat := 120597207583095596853223

theorem tailTrace_1056880 : CollatzResearch.WordTrace tailWord_1056880 prefixEnd_1056880 120597207583095596853223 := by
  unfold tailWord_1056880
  simp only [CollatzResearch.WordTrace]
  refine ⟨19273790205555867789356047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25698386940741157052474729 19273790205555867789356047)
  ·
    refine ⟨28910685308333801684034071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19273790205555867789356047 28910685308333801684034071)
    ·
      refine ⟨43366027962500702526051107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28910685308333801684034071 43366027962500702526051107)
      ·
        refine ⟨65049041943751053789076661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43366027962500702526051107 65049041943751053789076661)
        ·
          refine ⟨6098347682226661292725937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65049041943751053789076661 6098347682226661292725937)
          ·
            refine ⟨4573760761669995969544453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6098347682226661292725937 4573760761669995969544453)
            ·
              refine ⟨857580142813124244289585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4573760761669995969544453 857580142813124244289585)
              ·
                refine ⟨643185107109843183217189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 857580142813124244289585 643185107109843183217189)
                ·
                  refine ⟨120597207583095596853223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 643185107109843183217189 120597207583095596853223)
                  ·
                    rfl

theorem cell22_1056880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 2, 4].length) (baseStart_1056880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1056880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1056880 prefixEnd_1056880 := by exact prefixLift 1056880
  have htrace : WordTrace (prefixWord ++ tailWord_1056880) baseStart_1056880 baseEnd_1056880 := by
    simpa [prefixWord, tailWord_1056880, baseEnd_1056880] using wordTrace_append hprefix tailTrace_1056880
  have hstable : (prefixWord ++ tailWord_1056880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056880).length < 2 ^ (prefixWord ++ tailWord_1056880).sum := by decide
  have hdescent : baseEnd_1056880 < baseStart_1056880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056916 : List Nat := [2, 4, 2, 3, 2, 1, 2, 1, 1, 4]
def baseStart_1056916 : Nat := 118140960795 + 1056916 * 2 ^ 59
def prefixEnd_1056916 : Nat := 4983230072969 + 3 ^ 40 * 1056916 * 2
def baseEnd_1056916 : Nat := 361803946284994696659559

theorem tailTrace_1056916 : CollatzResearch.WordTrace tailWord_1056916 prefixEnd_1056916 361803946284994696659559 := by
  unfold tailWord_1056916
  simp only [CollatzResearch.WordTrace]
  refine ⟨19274446719490656863511301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25699262292654209151348401 19274446719490656863511301)
  ·
    refine ⟨3613958759904498161908369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19274446719490656863511301 3613958759904498161908369)
    ·
      refine ⟨2710469069928373621431277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3613958759904498161908369 2710469069928373621431277)
      ·
        refine ⟨1016425901223140108036729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2710469069928373621431277 1016425901223140108036729)
        ·
          refine ⟨762319425917355081027547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1016425901223140108036729 762319425917355081027547)
          ·
            refine ⟨1143479138876032621541321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 762319425917355081027547 1143479138876032621541321)
            ·
              refine ⟨857609354157024466155991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1143479138876032621541321 857609354157024466155991)
              ·
                refine ⟨1286414031235536699233987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 857609354157024466155991 1286414031235536699233987)
                ·
                  refine ⟨1929621046853305048850981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1286414031235536699233987 1929621046853305048850981)
                  ·
                    refine ⟨361803946284994696659559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1929621046853305048850981 361803946284994696659559)
                    ·
                      rfl

theorem cell22_1056916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_1056916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1056916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1056916 prefixEnd_1056916 := by exact prefixLift 1056916
  have htrace : WordTrace (prefixWord ++ tailWord_1056916) baseStart_1056916 baseEnd_1056916 := by
    simpa [prefixWord, tailWord_1056916, baseEnd_1056916] using wordTrace_append hprefix tailTrace_1056916
  have hstable : (prefixWord ++ tailWord_1056916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056916).length < 2 ^ (prefixWord ++ tailWord_1056916).sum := by decide
  have hdescent : baseEnd_1056916 < baseStart_1056916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056974 : List Nat := [4, 1, 1, 1, 4, 3, 1, 3, 1, 3]
def baseStart_1056974 : Nat := 118140960795 + 1056974 * 2 ^ 59
def prefixEnd_1056974 : Nat := 4983230072969 + 3 ^ 40 * 1056974 * 2
def baseEnd_1056974 : Nat := 361823800870301878709381

theorem tailTrace_1056974 : CollatzResearch.WordTrace tailWord_1056974 prefixEnd_1056974 361823800870301878709381 := by
  unfold tailWord_1056974
  simp only [CollatzResearch.WordTrace]
  refine ⟨4818876109096398704079247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25700672581847459755089317 4818876109096398704079247)
  ·
    refine ⟨7228314163644598056118871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4818876109096398704079247 7228314163644598056118871)
    ·
      refine ⟨10842471245466897084178307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7228314163644598056118871 10842471245466897084178307)
      ·
        refine ⟨16263706868200345626267461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10842471245466897084178307 16263706868200345626267461)
        ·
          refine ⟨3049445037787564804925149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16263706868200345626267461 3049445037787564804925149)
          ·
            refine ⟨1143541889170336801846931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3049445037787564804925149 1143541889170336801846931)
            ·
              refine ⟨1715312833755505202770397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1143541889170336801846931 1715312833755505202770397)
              ·
                refine ⟨643242312658314451038899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1715312833755505202770397 643242312658314451038899)
                ·
                  refine ⟨964863468987471676558349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 643242312658314451038899 964863468987471676558349)
                  ·
                    refine ⟨361823800870301878709381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 964863468987471676558349 361823800870301878709381)
                    ·
                      rfl

theorem cell22_1056974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 3, 1, 3].length) (baseStart_1056974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1056974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1056974 prefixEnd_1056974 := by exact prefixLift 1056974
  have htrace : WordTrace (prefixWord ++ tailWord_1056974) baseStart_1056974 baseEnd_1056974 := by
    simpa [prefixWord, tailWord_1056974, baseEnd_1056974] using wordTrace_append hprefix tailTrace_1056974
  have hstable : (prefixWord ++ tailWord_1056974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056974).length < 2 ^ (prefixWord ++ tailWord_1056974).sum := by decide
  have hdescent : baseEnd_1056974 < baseStart_1056974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057047 : List Nat := [1, 1, 3, 4, 1, 3, 2, 2, 2, 3]
def baseStart_1057047 : Nat := 118140960795 + 1057047 * 2 ^ 59
def prefixEnd_1057047 : Nat := 4983230072969 + 3 ^ 40 * 1057047 * 2
def baseEnd_1057047 : Nat := 361848790262154021634157

theorem tailTrace_1057047 : CollatzResearch.WordTrace tailWord_1057047 prefixEnd_1057047 361848790262154021634157 := by
  unfold tailWord_1057047
  simp only [CollatzResearch.WordTrace]
  refine ⟨38553671401506723100041395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25702447601004482066694263 38553671401506723100041395)
  ·
    refine ⟨57830507102260084650062093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38553671401506723100041395 57830507102260084650062093)
    ·
      refine ⟨21686440163347531743773285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57830507102260084650062093 21686440163347531743773285)
      ·
        refine ⟨4066207530627662201957491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21686440163347531743773285 4066207530627662201957491)
        ·
          refine ⟨6099311295941493302936237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4066207530627662201957491 6099311295941493302936237)
          ·
            refine ⟨2287241735978059988601089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6099311295941493302936237 2287241735978059988601089)
            ·
              refine ⟨1715431301983544991450817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2287241735978059988601089 1715431301983544991450817)
              ·
                refine ⟨1286573476487658743588113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1715431301983544991450817 1286573476487658743588113)
                ·
                  refine ⟨964930107365744057691085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1286573476487658743588113 964930107365744057691085)
                  ·
                    refine ⟨361848790262154021634157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 964930107365744057691085 361848790262154021634157)
                    ·
                      rfl

theorem cell22_1057047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 2, 2, 3].length) (baseStart_1057047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1057047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1057047 prefixEnd_1057047 := by exact prefixLift 1057047
  have htrace : WordTrace (prefixWord ++ tailWord_1057047) baseStart_1057047 baseEnd_1057047 := by
    simpa [prefixWord, tailWord_1057047, baseEnd_1057047] using wordTrace_append hprefix tailTrace_1057047
  have hstable : (prefixWord ++ tailWord_1057047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057047).length < 2 ^ (prefixWord ++ tailWord_1057047).sum := by decide
  have hdescent : baseEnd_1057047 < baseStart_1057047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057060 : List Nat := [2, 3, 1, 3, 1, 4, 1, 7]
def baseStart_1057060 : Nat := 118140960795 + 1057060 * 2 ^ 59
def prefixEnd_1057060 : Nat := 4983230072969 + 3 ^ 40 * 1057060 * 2
def baseEnd_1057060 : Nat := 40205915603091813451013

theorem tailTrace_1057060 : CollatzResearch.WordTrace tailWord_1057060 prefixEnd_1057060 40205915603091813451013 := by
  unfold tailWord_1057060
  simp only [CollatzResearch.WordTrace]
  refine ⟨19277072775229813160132317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25702763700306417546843089 19277072775229813160132317)
  ·
    refine ⟨7228902290711179935049619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19277072775229813160132317 7228902290711179935049619)
    ·
      refine ⟨10843353436066769902574429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7228902290711179935049619 10843353436066769902574429)
      ·
        refine ⟨4066257538525038713465411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10843353436066769902574429 4066257538525038713465411)
        ·
          refine ⟨6099386307787558070198117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4066257538525038713465411 6099386307787558070198117)
          ·
            refine ⟨1143634932710167138162147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6099386307787558070198117 1143634932710167138162147)
            ·
              refine ⟨1715452399065250707243221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1143634932710167138162147 1715452399065250707243221)
              ·
                refine ⟨40205915603091813451013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1715452399065250707243221 40205915603091813451013)
                ·
                  rfl

theorem cell22_1057060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 7].length) (baseStart_1057060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1057060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1057060 prefixEnd_1057060 := by exact prefixLift 1057060
  have htrace : WordTrace (prefixWord ++ tailWord_1057060) baseStart_1057060 baseEnd_1057060 := by
    simpa [prefixWord, tailWord_1057060, baseEnd_1057060] using wordTrace_append hprefix tailTrace_1057060
  have hstable : (prefixWord ++ tailWord_1057060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057060).length < 2 ^ (prefixWord ++ tailWord_1057060).sum := by decide
  have hdescent : baseEnd_1057060 < baseStart_1057060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057075 : List Nat := [1, 1, 1, 2, 5, 1, 3, 2, 3, 3]
def baseStart_1057075 : Nat := 118140960795 + 1057075 * 2 ^ 59
def prefixEnd_1057075 : Nat := 4983230072969 + 3 ^ 40 * 1057075 * 2
def baseEnd_1057075 : Nat := 361858375234371281934071

theorem tailTrace_1057075 : CollatzResearch.WordTrace tailWord_1057075 prefixEnd_1057075 361858375234371281934071 := by
  unfold tailWord_1057075
  simp only [CollatzResearch.WordTrace]
  refine ⟨38554692645405283882060679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25703128430270189254707119 38554692645405283882060679)
  ·
    refine ⟨57832038968107925823091019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38554692645405283882060679 57832038968107925823091019)
    ·
      refine ⟨86748058452161888734636529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57832038968107925823091019 86748058452161888734636529)
      ·
        refine ⟨65061043839121416550977397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86748058452161888734636529 65061043839121416550977397)
        ·
          refine ⟨6099472859917632801654131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65061043839121416550977397 6099472859917632801654131)
          ·
            refine ⟨9149209289876449202481197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6099472859917632801654131 9149209289876449202481197)
            ·
              refine ⟨3430953483703668450930449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9149209289876449202481197 3430953483703668450930449)
              ·
                refine ⟨2573215112777751338197837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3430953483703668450930449 2573215112777751338197837)
                ·
                  refine ⟨964955667291656751824189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2573215112777751338197837 964955667291656751824189)
                  ·
                    refine ⟨361858375234371281934071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 964955667291656751824189 361858375234371281934071)
                    ·
                      rfl

theorem cell22_1057075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 3, 3].length) (baseStart_1057075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1057075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1057075 prefixEnd_1057075 := by exact prefixLift 1057075
  have htrace : WordTrace (prefixWord ++ tailWord_1057075) baseStart_1057075 baseEnd_1057075 := by
    simpa [prefixWord, tailWord_1057075, baseEnd_1057075] using wordTrace_append hprefix tailTrace_1057075
  have hstable : (prefixWord ++ tailWord_1057075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057075).length < 2 ^ (prefixWord ++ tailWord_1057075).sum := by decide
  have hdescent : baseEnd_1057075 < baseStart_1057075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057105 : List Nat := [1, 2, 2, 1, 4, 2, 3, 2, 5]
def baseStart_1057105 : Nat := 118140960795 + 1057105 * 2 ^ 59
def prefixEnd_1057105 : Nat := 4983230072969 + 3 ^ 40 * 1057105 * 2
def baseEnd_1057105 : Nat := 120622881615820401227993

theorem tailTrace_1057105 : CollatzResearch.WordTrace tailWord_1057105 prefixEnd_1057105 120622881615820401227993 := by
  unfold tailWord_1057105
  simp only [CollatzResearch.WordTrace]
  refine ⟨38555786835296599005652769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25703857890197732670435179 38555786835296599005652769)
  ·
    refine ⟨28916840126472449254239577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38555786835296599005652769 28916840126472449254239577)
    ·
      refine ⟨21687630094854336940679683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28916840126472449254239577 21687630094854336940679683)
      ·
        refine ⟨32531445142281505411019525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21687630094854336940679683 32531445142281505411019525)
        ·
          refine ⟨6099645964177782264566161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32531445142281505411019525 6099645964177782264566161)
          ·
            refine ⟨4574734473133336698424621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6099645964177782264566161 4574734473133336698424621)
            ·
              refine ⟨1715525427425001261909233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4574734473133336698424621 1715525427425001261909233)
              ·
                refine ⟨1286644070568750946431925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1715525427425001261909233 1286644070568750946431925)
                ·
                  refine ⟨120622881615820401227993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1286644070568750946431925 120622881615820401227993)
                  ·
                    rfl

theorem cell22_1057105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 2, 5].length) (baseStart_1057105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1057105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1057105 prefixEnd_1057105 := by exact prefixLift 1057105
  have htrace : WordTrace (prefixWord ++ tailWord_1057105) baseStart_1057105 baseEnd_1057105 := by
    simpa [prefixWord, tailWord_1057105, baseEnd_1057105] using wordTrace_append hprefix tailTrace_1057105
  have hstable : (prefixWord ++ tailWord_1057105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057105).length < 2 ^ (prefixWord ++ tailWord_1057105).sum := by decide
  have hdescent : baseEnd_1057105 < baseStart_1057105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057193 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 2, 7]
def baseStart_1057193 : Nat := 118140960795 + 1057193 * 2 ^ 59
def prefixEnd_1057193 : Nat := 4983230072969 + 3 ^ 40 * 1057193 * 2
def baseEnd_1057193 : Nat := 361898769045858307483709

theorem tailTrace_1057193 : CollatzResearch.WordTrace tailWord_1057193 prefixEnd_1057193 361898769045858307483709 := by
  unfold tailWord_1057193
  simp only [CollatzResearch.WordTrace]
  refine ⟨38558996458977790034856233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25705997639318526689904155 38558996458977790034856233)
  ·
    refine ⟨28919247344233342526142175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38558996458977790034856233 28919247344233342526142175)
    ·
      refine ⟨43378871016350013789213263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28919247344233342526142175 43378871016350013789213263)
      ·
        refine ⟨65068306524525020683819895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43378871016350013789213263 65068306524525020683819895)
        ·
          refine ⟨97602459786787531025729843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65068306524525020683819895 97602459786787531025729843)
          ·
            refine ⟨146403689680181296538594765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97602459786787531025729843 146403689680181296538594765)
            ·
              refine ⟨54901383630067986201973037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 146403689680181296538594765 54901383630067986201973037)
              ·
                refine ⟨20588018861275494825739889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54901383630067986201973037 20588018861275494825739889)
                ·
                  refine ⟨15441014145956621119304917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20588018861275494825739889 15441014145956621119304917)
                  ·
                    refine ⟨361898769045858307483709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15441014145956621119304917 361898769045858307483709)
                    ·
                      rfl

theorem cell22_1057193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 7].length) (baseStart_1057193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1057193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1057193 prefixEnd_1057193 := by exact prefixLift 1057193
  have htrace : WordTrace (prefixWord ++ tailWord_1057193) baseStart_1057193 baseEnd_1057193 := by
    simpa [prefixWord, tailWord_1057193, baseEnd_1057193] using wordTrace_append hprefix tailTrace_1057193
  have hstable : (prefixWord ++ tailWord_1057193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057193).length < 2 ^ (prefixWord ++ tailWord_1057193).sum := by decide
  have hdescent : baseEnd_1057193 < baseStart_1057193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057255 : List Nat := [1, 1, 5, 2, 1, 1, 1, 2, 1, 7]
def baseStart_1057255 : Nat := 118140960795 + 1057255 * 2 ^ 59
def prefixEnd_1057255 : Nat := 4983230072969 + 3 ^ 40 * 1057255 * 2
def baseEnd_1057255 : Nat := 361919992912910812433519

theorem tailTrace_1057255 : CollatzResearch.WordTrace tailWord_1057255 prefixEnd_1057255 361919992912910812433519 := by
  unfold tailWord_1057255
  simp only [CollatzResearch.WordTrace]
  refine ⟨38561257784753174623613219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25707505189835449749075479 38561257784753174623613219)
  ·
    refine ⟨57841886677129761935419829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38561257784753174623613219 57841886677129761935419829)
    ·
      refine ⟨5422676875980915181445609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57841886677129761935419829 5422676875980915181445609)
      ·
        refine ⟨4067007656985686386084207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5422676875980915181445609 4067007656985686386084207)
        ·
          refine ⟨6100511485478529579126311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4067007656985686386084207 6100511485478529579126311)
          ·
            refine ⟨9150767228217794368689467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6100511485478529579126311 9150767228217794368689467)
            ·
              refine ⟨13726150842326691553034201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9150767228217794368689467 13726150842326691553034201)
              ·
                refine ⟨10294613131745018664775651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13726150842326691553034201 10294613131745018664775651)
                ·
                  refine ⟨15441919697617527997163477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10294613131745018664775651 15441919697617527997163477)
                  ·
                    refine ⟨361919992912910812433519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15441919697617527997163477 361919992912910812433519)
                    ·
                      rfl

theorem cell22_1057255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_1057255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1057255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1057255 prefixEnd_1057255 := by exact prefixLift 1057255
  have htrace : WordTrace (prefixWord ++ tailWord_1057255) baseStart_1057255 baseEnd_1057255 := by
    simpa [prefixWord, tailWord_1057255, baseEnd_1057255] using wordTrace_append hprefix tailTrace_1057255
  have hstable : (prefixWord ++ tailWord_1057255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057255).length < 2 ^ (prefixWord ++ tailWord_1057255).sum := by decide
  have hdescent : baseEnd_1057255 < baseStart_1057255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057261 : List Nat := [1, 5, 1, 3, 1, 1, 1, 5, 1, 3]
def baseStart_1057261 : Nat := 118140960795 + 1057261 * 2 ^ 59
def prefixEnd_1057261 : Nat := 4983230072969 + 3 ^ 40 * 1057261 * 2
def baseEnd_1057261 : Nat := 361922046835528796783501

theorem tailTrace_1057261 : CollatzResearch.WordTrace tailWord_1057261 prefixEnd_1057261 361922046835528796783501 := by
  unfold tailWord_1057261
  simp only [CollatzResearch.WordTrace]
  refine ⟨38561476622731437648331637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25707651081820958432221091 38561476622731437648331637)
  ·
    refine ⟨3615138433381072279531091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38561476622731437648331637 3615138433381072279531091)
    ·
      refine ⟨5422707650071608419296637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3615138433381072279531091 5422707650071608419296637)
      ·
        refine ⟨2033515368776853157236239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5422707650071608419296637 2033515368776853157236239)
        ·
          refine ⟨3050273053165279735854359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2033515368776853157236239 3050273053165279735854359)
          ·
            refine ⟨4575409579747919603781539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3050273053165279735854359 4575409579747919603781539)
            ·
              refine ⟨6863114369621879405672309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4575409579747919603781539 6863114369621879405672309)
              ·
                refine ⟨643416972152051194281779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6863114369621879405672309 643416972152051194281779)
                ·
                  refine ⟨965125458228076791422669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 643416972152051194281779 965125458228076791422669)
                  ·
                    refine ⟨361922046835528796783501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 965125458228076791422669 361922046835528796783501)
                    ·
                      rfl

theorem cell22_1057261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_1057261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1057261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1057261 prefixEnd_1057261 := by exact prefixLift 1057261
  have htrace : WordTrace (prefixWord ++ tailWord_1057261) baseStart_1057261 baseEnd_1057261 := by
    simpa [prefixWord, tailWord_1057261, baseEnd_1057261] using wordTrace_append hprefix tailTrace_1057261
  have hstable : (prefixWord ++ tailWord_1057261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057261).length < 2 ^ (prefixWord ++ tailWord_1057261).sum := by decide
  have hdescent : baseEnd_1057261 < baseStart_1057261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057285 : List Nat := [1, 3, 1, 1, 2, 2, 3, 3, 6]
def baseStart_1057285 : Nat := 118140960795 + 1057285 * 2 ^ 59
def prefixEnd_1057285 : Nat := 4983230072969 + 3 ^ 40 * 1057285 * 2
def baseEnd_1057285 : Nat := 120643420842000244727809

theorem tailTrace_1057285 : CollatzResearch.WordTrace tailWord_1057285 prefixEnd_1057285 120643420842000244727809 := by
  unfold tailWord_1057285
  simp only [CollatzResearch.WordTrace]
  refine ⟨38562351974644489747205309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25708234649762993164803539 38562351974644489747205309)
  ·
    refine ⟨14460881990491683655201991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38562351974644489747205309 14460881990491683655201991)
    ·
      refine ⟨21691322985737525482802987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14460881990491683655201991 21691322985737525482802987)
      ·
        refine ⟨32536984478606288224204481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21691322985737525482802987 32536984478606288224204481)
        ·
          refine ⟨24402738358954716168153361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32536984478606288224204481 24402738358954716168153361)
          ·
            refine ⟨18302053769216037126115021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24402738358954716168153361 18302053769216037126115021)
            ·
              refine ⟨6863270163456013922293133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18302053769216037126115021 6863270163456013922293133)
              ·
                refine ⟨2573726311296005220859925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6863270163456013922293133 2573726311296005220859925)
                ·
                  refine ⟨120643420842000244727809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2573726311296005220859925 120643420842000244727809)
                  ·
                    rfl

theorem cell22_1057285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 6].length) (baseStart_1057285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1057285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1057285 prefixEnd_1057285 := by exact prefixLift 1057285
  have htrace : WordTrace (prefixWord ++ tailWord_1057285) baseStart_1057285 baseEnd_1057285 := by
    simpa [prefixWord, tailWord_1057285, baseEnd_1057285] using wordTrace_append hprefix tailTrace_1057285
  have hstable : (prefixWord ++ tailWord_1057285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057285).length < 2 ^ (prefixWord ++ tailWord_1057285).sum := by decide
  have hdescent : baseEnd_1057285 < baseStart_1057285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057304 : List Nat := [2, 1, 2, 3, 3, 2, 2, 2, 1, 4]
def baseStart_1057304 : Nat := 118140960795 + 1057304 * 2 ^ 59
def prefixEnd_1057304 : Nat := 4983230072969 + 3 ^ 40 * 1057304 * 2
def baseEnd_1057304 : Nat := 361936766614291017958369

theorem tailTrace_1057304 : CollatzResearch.WordTrace tailWord_1057304 prefixEnd_1057304 361936766614291017958369 := by
  unfold tailWord_1057304
  simp only [CollatzResearch.WordTrace]
  refine ⟨19281522480787827996073483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25708696641050437328097977 19281522480787827996073483)
  ·
    refine ⟨28922283721181741994110225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19281522480787827996073483 28922283721181741994110225)
    ·
      refine ⟨21691712790886306495582669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28922283721181741994110225 21691712790886306495582669)
      ·
        refine ⟨8134392296582364935843501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21691712790886306495582669 8134392296582364935843501)
        ·
          refine ⟨3050397111218386850941313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8134392296582364935843501 3050397111218386850941313)
          ·
            refine ⟨2287797833413790138205985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3050397111218386850941313 2287797833413790138205985)
            ·
              refine ⟨1715848375060342603654489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2287797833413790138205985 1715848375060342603654489)
              ·
                refine ⟨1286886281295256952740867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1715848375060342603654489 1286886281295256952740867)
                ·
                  refine ⟨1930329421942885429111301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1286886281295256952740867 1930329421942885429111301)
                  ·
                    refine ⟨361936766614291017958369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1930329421942885429111301 361936766614291017958369)
                    ·
                      rfl

theorem cell22_1057304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 2, 1, 4].length) (baseStart_1057304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1057304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1057304 prefixEnd_1057304 := by exact prefixLift 1057304
  have htrace : WordTrace (prefixWord ++ tailWord_1057304) baseStart_1057304 baseEnd_1057304 := by
    simpa [prefixWord, tailWord_1057304, baseEnd_1057304] using wordTrace_append hprefix tailTrace_1057304
  have hstable : (prefixWord ++ tailWord_1057304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057304).length < 2 ^ (prefixWord ++ tailWord_1057304).sum := by decide
  have hdescent : baseEnd_1057304 < baseStart_1057304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057317 : List Nat := [1, 3, 1, 2, 2, 1, 3, 2, 4, 3]
def baseStart_1057317 : Nat := 118140960795 + 1057317 * 2 ^ 59
def prefixEnd_1057317 : Nat := 4983230072969 + 3 ^ 40 * 1057317 * 2
def baseEnd_1057317 : Nat := 361941216779963317383329

theorem tailTrace_1057317 : CollatzResearch.WordTrace tailWord_1057317 prefixEnd_1057317 361941216779963317383329 := by
  unfold tailWord_1057317
  simp only [CollatzResearch.WordTrace]
  refine ⟨38563519110528559212370205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25709012740352372808246803 38563519110528559212370205)
  ·
    refine ⟨14461319666448209704638827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38563519110528559212370205 14461319666448209704638827)
    ·
      refine ⟨21691979499672314556958241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14461319666448209704638827 21691979499672314556958241)
      ·
        refine ⟨16268984624754235917718681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21691979499672314556958241 16268984624754235917718681)
        ·
          refine ⟨12201738468565676938289011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16268984624754235917718681 12201738468565676938289011)
          ·
            refine ⟨18302607702848515407433517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12201738468565676938289011 18302607702848515407433517)
            ·
              refine ⟨6863477888568193277787569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18302607702848515407433517 6863477888568193277787569)
              ·
                refine ⟨5147608416426144958340677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6863477888568193277787569 5147608416426144958340677)
                ·
                  refine ⟨965176578079902179688877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5147608416426144958340677 965176578079902179688877)
                  ·
                    refine ⟨361941216779963317383329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 965176578079902179688877 361941216779963317383329)
                    ·
                      rfl

theorem cell22_1057317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 4, 3].length) (baseStart_1057317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1057317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1057317 prefixEnd_1057317 := by exact prefixLift 1057317
  have htrace : WordTrace (prefixWord ++ tailWord_1057317) baseStart_1057317 baseEnd_1057317 := by
    simpa [prefixWord, tailWord_1057317, baseEnd_1057317] using wordTrace_append hprefix tailTrace_1057317
  have hstable : (prefixWord ++ tailWord_1057317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057317).length < 2 ^ (prefixWord ++ tailWord_1057317).sum := by decide
  have hdescent : baseEnd_1057317 < baseStart_1057317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057330 : List Nat := [3, 2, 1, 1, 2, 1, 12]
def baseStart_1057330 : Nat := 118140960795 + 1057330 * 2 ^ 59
def prefixEnd_1057330 : Nat := 4983230072969 + 3 ^ 40 * 1057330 * 2
def baseEnd_1057330 : Nat := 13405395072060578400307

theorem tailTrace_1057330 : CollatzResearch.WordTrace tailWord_1057330 prefixEnd_1057330 13405395072060578400307 := by
  unfold tailWord_1057330
  simp only [CollatzResearch.WordTrace]
  refine ⟨9640998314870365608148361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25709328839654308288395629 9640998314870365608148361)
  ·
    refine ⟨7230748736152774206111271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9640998314870365608148361 7230748736152774206111271)
    ·
      refine ⟨10846123104229161309166907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7230748736152774206111271 10846123104229161309166907)
      ·
        refine ⟨16269184656343741963750361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10846123104229161309166907 16269184656343741963750361)
        ·
          refine ⟨12201888492257806472812771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16269184656343741963750361 12201888492257806472812771)
          ·
            refine ⟨18302832738386709709219157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12201888492257806472812771 18302832738386709709219157)
            ·
              refine ⟨13405395072060578400307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 18302832738386709709219157 13405395072060578400307)
              ·
                rfl

theorem cell22_1057330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 12].length) (baseStart_1057330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1057330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1057330 prefixEnd_1057330 := by exact prefixLift 1057330
  have htrace : WordTrace (prefixWord ++ tailWord_1057330) baseStart_1057330 baseEnd_1057330 := by
    simpa [prefixWord, tailWord_1057330, baseEnd_1057330] using wordTrace_append hprefix tailTrace_1057330
  have hstable : (prefixWord ++ tailWord_1057330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057330).length < 2 ^ (prefixWord ++ tailWord_1057330).sum := by decide
  have hdescent : baseEnd_1057330 < baseStart_1057330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057351 : List Nat := [1, 1, 4, 1, 4, 1, 4, 1, 2, 3]
def baseStart_1057351 : Nat := 118140960795 + 1057351 * 2 ^ 59
def prefixEnd_1057351 : Nat := 4983230072969 + 3 ^ 40 * 1057351 * 2
def baseEnd_1057351 : Nat := 361952855674798562033225

theorem tailTrace_1057351 : CollatzResearch.WordTrace tailWord_1057351 prefixEnd_1057351 361952855674798562033225 := by
  unfold tailWord_1057351
  simp only [CollatzResearch.WordTrace]
  refine ⟨38564759192405383019107907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25709839461603588679405271 38564759192405383019107907)
  ·
    refine ⟨57847138788608074528661861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38564759192405383019107907 57847138788608074528661861)
    ·
      refine ⟨10846338522864013974124099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57847138788608074528661861 10846338522864013974124099)
      ·
        refine ⟨16269507784296020961186149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10846338522864013974124099 16269507784296020961186149)
        ·
          refine ⟨3050532709555503930222403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16269507784296020961186149 3050532709555503930222403)
          ·
            refine ⟨4575799064333255895333605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3050532709555503930222403 4575799064333255895333605)
            ·
              refine ⟨857962324562485480375051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4575799064333255895333605 857962324562485480375051)
              ·
                refine ⟨1286943486843728220562577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 857962324562485480375051 1286943486843728220562577)
                ·
                  refine ⟨965207615132796165421933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1286943486843728220562577 965207615132796165421933)
                  ·
                    refine ⟨361952855674798562033225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 965207615132796165421933 361952855674798562033225)
                    ·
                      rfl

theorem cell22_1057351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 1, 2, 3].length) (baseStart_1057351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1057351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1057351 prefixEnd_1057351 := by exact prefixLift 1057351
  have htrace : WordTrace (prefixWord ++ tailWord_1057351) baseStart_1057351 baseEnd_1057351 := by
    simpa [prefixWord, tailWord_1057351, baseEnd_1057351] using wordTrace_append hprefix tailTrace_1057351
  have hstable : (prefixWord ++ tailWord_1057351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057351).length < 2 ^ (prefixWord ++ tailWord_1057351).sum := by decide
  have hdescent : baseEnd_1057351 < baseStart_1057351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057360 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 4, 6]
def baseStart_1057360 : Nat := 118140960795 + 1057360 * 2 ^ 59
def prefixEnd_1057360 : Nat := 4983230072969 + 3 ^ 40 * 1057360 * 2
def baseEnd_1057360 : Nat := 361955936558725538558197

theorem tailTrace_1057360 : CollatzResearch.WordTrace tailWord_1057360 prefixEnd_1057360 361955936558725538558197 := by
  unfold tailWord_1057360
  simp only [CollatzResearch.WordTrace]
  refine ⟨19282543724686388778092767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25710058299581851704123689 19282543724686388778092767)
  ·
    refine ⟨28923815587029583167139151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19282543724686388778092767 28923815587029583167139151)
    ·
      refine ⟨43385723380544374750708727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28923815587029583167139151 43385723380544374750708727)
      ·
        refine ⟨65078585070816562126063091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43385723380544374750708727 65078585070816562126063091)
        ·
          refine ⟨97617877606224843189094637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65078585070816562126063091 97617877606224843189094637)
          ·
            refine ⟨36606704102334316195910489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97617877606224843189094637 36606704102334316195910489)
            ·
              refine ⟨27455028076750737146932867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36606704102334316195910489 27455028076750737146932867)
              ·
                refine ⟨41182542115126105720399301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27455028076750737146932867 41182542115126105720399301)
                ·
                  refine ⟨7721726646586144822574869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41182542115126105720399301 7721726646586144822574869)
                  ·
                    refine ⟨361955936558725538558197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7721726646586144822574869 361955936558725538558197)
                    ·
                      rfl

theorem cell22_1057360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 4, 6].length) (baseStart_1057360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1057360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1057360 prefixEnd_1057360 := by exact prefixLift 1057360
  have htrace : WordTrace (prefixWord ++ tailWord_1057360) baseStart_1057360 baseEnd_1057360 := by
    simpa [prefixWord, tailWord_1057360, baseEnd_1057360] using wordTrace_append hprefix tailTrace_1057360
  have hstable : (prefixWord ++ tailWord_1057360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057360).length < 2 ^ (prefixWord ++ tailWord_1057360).sum := by decide
  have hdescent : baseEnd_1057360 < baseStart_1057360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057375 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 9]
def baseStart_1057375 : Nat := 118140960795 + 1057375 * 2 ^ 59
def prefixEnd_1057375 : Nat := 4983230072969 + 3 ^ 40 * 1057375 * 2
def baseEnd_1057375 : Nat := 120653690455090166477717

theorem tailTrace_1057375 : CollatzResearch.WordTrace tailWord_1057375 prefixEnd_1057375 120653690455090166477717 := by
  unfold tailWord_1057375
  simp only [CollatzResearch.WordTrace]
  refine ⟨38565634544318435117981579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25710423029545623411987719 38565634544318435117981579)
  ·
    refine ⟨57848451816477652676972369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38565634544318435117981579 57848451816477652676972369)
    ·
      refine ⟨43386338862358239507729277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57848451816477652676972369 43386338862358239507729277)
      ·
        refine ⟨16269877073384339815398479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43386338862358239507729277 16269877073384339815398479)
        ·
          refine ⟨24404815610076509723097719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16269877073384339815398479 24404815610076509723097719)
          ·
            refine ⟨36607223415114764584646579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24404815610076509723097719 36607223415114764584646579)
            ·
              refine ⟨54910835122672146876969869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36607223415114764584646579 54910835122672146876969869)
              ·
                refine ⟨20591563171002055078863701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54910835122672146876969869 20591563171002055078863701)
                ·
                  refine ⟨120653690455090166477717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 20591563171002055078863701 120653690455090166477717)
                  ·
                    rfl

theorem cell22_1057375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 9].length) (baseStart_1057375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1057375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1057375 prefixEnd_1057375 := by exact prefixLift 1057375
  have htrace : WordTrace (prefixWord ++ tailWord_1057375) baseStart_1057375 baseEnd_1057375 := by
    simpa [prefixWord, tailWord_1057375, baseEnd_1057375] using wordTrace_append hprefix tailTrace_1057375
  have hstable : (prefixWord ++ tailWord_1057375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057375).length < 2 ^ (prefixWord ++ tailWord_1057375).sum := by decide
  have hdescent : baseEnd_1057375 < baseStart_1057375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057469 : List Nat := [1, 4, 1, 2, 1, 3, 3, 1, 1, 5]
def baseStart_1057469 : Nat := 118140960795 + 1057469 * 2 ^ 59
def prefixEnd_1057469 : Nat := 4983230072969 + 3 ^ 40 * 1057469 * 2
def baseEnd_1057469 : Nat := 361993249486285587582863

theorem tailTrace_1057469 : CollatzResearch.WordTrace tailWord_1057469 prefixEnd_1057469 361993249486285587582863 := by
  unfold tailWord_1057469
  simp only [CollatzResearch.WordTrace]
  refine ⟨38569063005977889171903461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25712708670651926114602307 38569063005977889171903461)
  ·
    refine ⟨7231699313620854219731899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38569063005977889171903461 7231699313620854219731899)
    ·
      refine ⟨10847548970431281329597849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7231699313620854219731899 10847548970431281329597849)
      ·
        refine ⟨8135661727823460997198387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10847548970431281329597849 8135661727823460997198387)
        ·
          refine ⟨12203492591735191495797581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8135661727823460997198387 12203492591735191495797581)
          ·
            refine ⟨4576309721900696810924093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12203492591735191495797581 4576309721900696810924093)
            ·
              refine ⟨1716116145712761304096535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4576309721900696810924093 1716116145712761304096535)
              ·
                refine ⟨2574174218569141956144803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1716116145712761304096535 2574174218569141956144803)
                ·
                  refine ⟨3861261327853712934217205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2574174218569141956144803 3861261327853712934217205)
                  ·
                    refine ⟨361993249486285587582863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3861261327853712934217205 361993249486285587582863)
                    ·
                      rfl

theorem cell22_1057469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_1057469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1057469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1057469 prefixEnd_1057469 := by exact prefixLift 1057469
  have htrace : WordTrace (prefixWord ++ tailWord_1057469) baseStart_1057469 baseEnd_1057469 := by
    simpa [prefixWord, tailWord_1057469, baseEnd_1057469] using wordTrace_append hprefix tailTrace_1057469
  have hstable : (prefixWord ++ tailWord_1057469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057469).length < 2 ^ (prefixWord ++ tailWord_1057469).sum := by decide
  have hdescent : baseEnd_1057469 < baseStart_1057469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057484 : List Nat := [2, 2, 1, 5, 1, 1, 2, 1, 1, 6]
def baseStart_1057484 : Nat := 118140960795 + 1057484 * 2 ^ 59
def prefixEnd_1057484 : Nat := 4983230072969 + 3 ^ 40 * 1057484 * 2
def baseEnd_1057484 : Nat := 361998384292830548457817

theorem tailTrace_1057484 : CollatzResearch.WordTrace tailWord_1057484 prefixEnd_1057484 361998384292830548457817 := by
  unfold tailWord_1057484
  simp only [CollatzResearch.WordTrace]
  refine ⟨19284805050461773366849753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25713073400615697822466337 19284805050461773366849753)
  ·
    refine ⟨14463603787846330025137315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19284805050461773366849753 14463603787846330025137315)
    ·
      refine ⟨21695405681769495037705973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14463603787846330025137315 21695405681769495037705973)
      ·
        refine ⟨2033944282665890159784935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21695405681769495037705973 2033944282665890159784935)
        ·
          refine ⟨3050916423998835239677403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2033944282665890159784935 3050916423998835239677403)
          ·
            refine ⟨4576374635998252859516105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3050916423998835239677403 4576374635998252859516105)
            ·
              refine ⟨3432280976998689644637079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4576374635998252859516105 3432280976998689644637079)
              ·
                refine ⟨5148421465498034466955619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3432280976998689644637079 5148421465498034466955619)
                ·
                  refine ⟨7722632198247051700433429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5148421465498034466955619 7722632198247051700433429)
                  ·
                    refine ⟨361998384292830548457817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7722632198247051700433429 361998384292830548457817)
                    ·
                      rfl

theorem cell22_1057484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 1, 6].length) (baseStart_1057484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1057484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1057484 prefixEnd_1057484 := by exact prefixLift 1057484
  have htrace : WordTrace (prefixWord ++ tailWord_1057484) baseStart_1057484 baseEnd_1057484 := by
    simpa [prefixWord, tailWord_1057484, baseEnd_1057484] using wordTrace_append hprefix tailTrace_1057484
  have hstable : (prefixWord ++ tailWord_1057484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057484).length < 2 ^ (prefixWord ++ tailWord_1057484).sum := by decide
  have hdescent : baseEnd_1057484 < baseStart_1057484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057589 : List Nat := [1, 3, 3, 1, 3, 1, 1, 1, 8]
def baseStart_1057589 : Nat := 118140960795 + 1057589 * 2 ^ 59
def prefixEnd_1057589 : Nat := 4983230072969 + 3 ^ 40 * 1057589 * 2
def baseEnd_1057589 : Nat := 120678109312881758194165

theorem tailTrace_1057589 : CollatzResearch.WordTrace tailWord_1057589 prefixEnd_1057589 120678109312881758194165 := by
  unfold tailWord_1057589
  simp only [CollatzResearch.WordTrace]
  refine ⟨38573439765543149666271821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25715626510362099777514547 38573439765543149666271821)
  ·
    refine ⟨14465039912078681124851933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38573439765543149666271821 14465039912078681124851933)
    ·
      refine ⟨5424389967029505421819475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14465039912078681124851933 5424389967029505421819475)
      ·
        refine ⟨8136584950544258132729213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5424389967029505421819475 8136584950544258132729213)
        ·
          refine ⟨3051219356454096799773455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8136584950544258132729213 3051219356454096799773455)
          ·
            refine ⟨4576829034681145199660183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3051219356454096799773455 4576829034681145199660183)
            ·
              refine ⟨6865243552021717799490275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4576829034681145199660183 6865243552021717799490275)
              ·
                refine ⟨10297865328032576699235413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6865243552021717799490275 10297865328032576699235413)
                ·
                  refine ⟨120678109312881758194165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10297865328032576699235413 120678109312881758194165)
                  ·
                    rfl

theorem cell22_1057589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 8].length) (baseStart_1057589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1057589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1057589 prefixEnd_1057589 := by exact prefixLift 1057589
  have htrace : WordTrace (prefixWord ++ tailWord_1057589) baseStart_1057589 baseEnd_1057589 := by
    simpa [prefixWord, tailWord_1057589, baseEnd_1057589] using wordTrace_append hprefix tailTrace_1057589
  have hstable : (prefixWord ++ tailWord_1057589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057589).length < 2 ^ (prefixWord ++ tailWord_1057589).sum := by decide
  have hdescent : baseEnd_1057589 < baseStart_1057589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057619 : List Nat := [1, 1, 1, 2, 1, 1, 3, 6, 2, 4]
def baseStart_1057619 : Nat := 118140960795 + 1057619 * 2 ^ 59
def prefixEnd_1057619 : Nat := 4983230072969 + 3 ^ 40 * 1057619 * 2
def baseEnd_1057619 : Nat := 362044597551735196332403

theorem tailTrace_1057619 : CollatzResearch.WordTrace tailWord_1057619 prefixEnd_1057619 362044597551735196332403 := by
  unfold tailWord_1057619
  simp only [CollatzResearch.WordTrace]
  refine ⟨38574533955434464789863911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25716355970289643193242607 38574533955434464789863911)
  ·
    refine ⟨57861800933151697184795867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38574533955434464789863911 57861800933151697184795867)
    ·
      refine ⟨86792701399727545777193801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57861800933151697184795867 86792701399727545777193801)
      ·
        refine ⟨65094526049795659332895351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86792701399727545777193801 65094526049795659332895351)
        ·
          refine ⟨97641789074693488999343027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65094526049795659332895351 97641789074693488999343027)
          ·
            refine ⟨146462683612040233499014541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97641789074693488999343027 146462683612040233499014541)
            ·
              refine ⟨54923506354515087562130453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 146462683612040233499014541 54923506354515087562130453)
              ·
                refine ⟨2574539360367894729474865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54923506354515087562130453 2574539360367894729474865)
                ·
                  refine ⟨1930904520275921047106149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2574539360367894729474865 1930904520275921047106149)
                  ·
                    refine ⟨362044597551735196332403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1930904520275921047106149 362044597551735196332403)
                    ·
                      rfl

theorem cell22_1057619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 2, 4].length) (baseStart_1057619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1057619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1057619 prefixEnd_1057619 := by exact prefixLift 1057619
  have htrace : WordTrace (prefixWord ++ tailWord_1057619) baseStart_1057619 baseEnd_1057619 := by
    simpa [prefixWord, tailWord_1057619, baseEnd_1057619] using wordTrace_append hprefix tailTrace_1057619
  have hstable : (prefixWord ++ tailWord_1057619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057619).length < 2 ^ (prefixWord ++ tailWord_1057619).sum := by decide
  have hdescent : baseEnd_1057619 < baseStart_1057619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057621 : List Nat := [1, 3, 2, 2, 2, 1, 3, 1, 4, 3]
def baseStart_1057621 : Nat := 118140960795 + 1057621 * 2 ^ 59
def prefixEnd_1057621 : Nat := 4983230072969 + 3 ^ 40 * 1057621 * 2
def baseEnd_1057621 : Nat := 362045282192607857782397

theorem tailTrace_1057621 : CollatzResearch.WordTrace tailWord_1057621 prefixEnd_1057621 362045282192607857782397 := by
  unfold tailWord_1057621
  simp only [CollatzResearch.WordTrace]
  refine ⟨38574606901427219131436717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25716404600951479420957811 38574606901427219131436717)
  ·
    refine ⟨14465477588035207174288769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38574606901427219131436717 14465477588035207174288769)
    ·
      refine ⟨10849108191026405380716577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14465477588035207174288769 10849108191026405380716577)
      ·
        refine ⟨8136831143269804035537433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10849108191026405380716577 8136831143269804035537433)
        ·
          refine ⟨6102623357452353026653075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8136831143269804035537433 6102623357452353026653075)
          ·
            refine ⟨9153935036178529539979613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6102623357452353026653075 9153935036178529539979613)
            ·
              refine ⟨3432725638566948577492355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9153935036178529539979613 3432725638566948577492355)
              ·
                refine ⟨5149088457850422866238533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3432725638566948577492355 5149088457850422866238533)
                ·
                  refine ⟨965454085846954287419725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5149088457850422866238533 965454085846954287419725)
                  ·
                    refine ⟨362045282192607857782397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 965454085846954287419725 362045282192607857782397)
                    ·
                      rfl

theorem cell22_1057621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 4, 3].length) (baseStart_1057621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1057621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1057621 prefixEnd_1057621 := by exact prefixLift 1057621
  have htrace : WordTrace (prefixWord ++ tailWord_1057621) baseStart_1057621 baseEnd_1057621 := by
    simpa [prefixWord, tailWord_1057621, baseEnd_1057621] using wordTrace_append hprefix tailTrace_1057621
  have hstable : (prefixWord ++ tailWord_1057621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057621).length < 2 ^ (prefixWord ++ tailWord_1057621).sum := by decide
  have hdescent : baseEnd_1057621 < baseStart_1057621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057818 : List Nat := [3, 1, 1, 3, 1, 2, 1, 4, 3, 3]
def baseStart_1057818 : Nat := 118140960795 + 1057818 * 2 ^ 59
def prefixEnd_1057818 : Nat := 4983230072969 + 3 ^ 40 * 1057818 * 2
def baseEnd_1057818 : Nat := 362112719318565010606793

theorem tailTrace_1057818 : CollatzResearch.WordTrace tailWord_1057818 prefixEnd_1057818 362112719318565010606793 := by
  unfold tailWord_1057818
  simp only [CollatzResearch.WordTrace]
  refine ⟨9645448020428380444089527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25721194721142347850905405 9645448020428380444089527)
  ·
    refine ⟨14468172030642570666134291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9645448020428380444089527 14468172030642570666134291)
    ·
      refine ⟨21702258045963855999201437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14468172030642570666134291 21702258045963855999201437)
      ·
        refine ⟨8138346767236445999700539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21702258045963855999201437 8138346767236445999700539)
        ·
          refine ⟨12207520150854668999550809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8138346767236445999700539 12207520150854668999550809)
          ·
            refine ⟨9155640113141001749663107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12207520150854668999550809 9155640113141001749663107)
            ·
              refine ⟨13733460169711502624494661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9155640113141001749663107 13733460169711502624494661)
              ·
                refine ⟨2575023781820906742092749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13733460169711502624494661 2575023781820906742092749)
                ·
                  refine ⟨965633918182840028284781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2575023781820906742092749 965633918182840028284781)
                  ·
                    refine ⟨362112719318565010606793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 965633918182840028284781 362112719318565010606793)
                    ·
                      rfl

theorem cell22_1057818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 3, 3].length) (baseStart_1057818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1057818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1057818 prefixEnd_1057818 := by exact prefixLift 1057818
  have htrace : WordTrace (prefixWord ++ tailWord_1057818) baseStart_1057818 baseEnd_1057818 := by
    simpa [prefixWord, tailWord_1057818, baseEnd_1057818] using wordTrace_append hprefix tailTrace_1057818
  have hstable : (prefixWord ++ tailWord_1057818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057818).length < 2 ^ (prefixWord ++ tailWord_1057818).sum := by decide
  have hdescent : baseEnd_1057818 < baseStart_1057818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057820 : List Nat := [2, 2, 3, 1, 4, 2, 2, 6]
def baseStart_1057820 : Nat := 118140960795 + 1057820 * 2 ^ 59
def prefixEnd_1057820 : Nat := 4983230072969 + 3 ^ 40 * 1057820 * 2
def baseEnd_1057820 : Nat := 40234822662159741339643

theorem tailTrace_1057820 : CollatzResearch.WordTrace tailWord_1057820 prefixEnd_1057820 40234822662159741339643 := by
  unfold tailWord_1057820
  simp only [CollatzResearch.WordTrace]
  refine ⟨19290932513853138058965457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25721243351804184078620609 19290932513853138058965457)
  ·
    refine ⟨14468199385389853544224093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19290932513853138058965457 14468199385389853544224093)
    ·
      refine ⟨5425574769521195079084035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14468199385389853544224093 5425574769521195079084035)
      ·
        refine ⟨8138362154281792618626053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5425574769521195079084035 8138362154281792618626053)
        ·
          refine ⟨1525942903927836115992385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8138362154281792618626053 1525942903927836115992385)
          ·
            refine ⟨1144457177945877086994289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1525942903927836115992385 1144457177945877086994289)
            ·
              refine ⟨858342883459407815245717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1144457177945877086994289 858342883459407815245717)
              ·
                refine ⟨40234822662159741339643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 858342883459407815245717 40234822662159741339643)
                ·
                  rfl

theorem cell22_1057820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 6].length) (baseStart_1057820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1057820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1057820 prefixEnd_1057820 := by exact prefixLift 1057820
  have htrace : WordTrace (prefixWord ++ tailWord_1057820) baseStart_1057820 baseEnd_1057820 := by
    simpa [prefixWord, tailWord_1057820, baseEnd_1057820] using wordTrace_append hprefix tailTrace_1057820
  have hstable : (prefixWord ++ tailWord_1057820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057820).length < 2 ^ (prefixWord ++ tailWord_1057820).sum := by decide
  have hdescent : baseEnd_1057820 < baseStart_1057820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057925 : List Nat := [1, 3, 1, 1, 6, 1, 2, 1, 1, 5]
def baseStart_1057925 : Nat := 118140960795 + 1057925 * 2 ^ 59
def prefixEnd_1057925 : Nat := 4983230072969 + 3 ^ 40 * 1057925 * 2
def baseEnd_1057925 : Nat := 362149347605252398181465

theorem tailTrace_1057925 : CollatzResearch.WordTrace tailWord_1057925 prefixEnd_1057925 362149347605252398181465 := by
  unfold tailWord_1057925
  simp only [CollatzResearch.WordTrace]
  refine ⟨38585694692325879050503229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25723796461550586033668819 38585694692325879050503229)
  ·
    refine ⟨14469635509622204643938711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38585694692325879050503229 14469635509622204643938711)
    ·
      refine ⟨21704453264433306965908067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14469635509622204643938711 21704453264433306965908067)
      ·
        refine ⟨32556679896649960448862101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21704453264433306965908067 32556679896649960448862101)
        ·
          refine ⟨1526094370155466896040411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 32556679896649960448862101 1526094370155466896040411)
          ·
            refine ⟨2289141555233200344060617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1526094370155466896040411 2289141555233200344060617)
            ·
              refine ⟨1716856166424900258045463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2289141555233200344060617 1716856166424900258045463)
              ·
                refine ⟨2575284249637350387068195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1716856166424900258045463 2575284249637350387068195)
                ·
                  refine ⟨3862926374456025580602293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2575284249637350387068195 3862926374456025580602293)
                  ·
                    refine ⟨362149347605252398181465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3862926374456025580602293 362149347605252398181465)
                    ·
                      rfl

theorem cell22_1057925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 5].length) (baseStart_1057925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1057925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1057925 prefixEnd_1057925 := by exact prefixLift 1057925
  have htrace : WordTrace (prefixWord ++ tailWord_1057925) baseStart_1057925 baseEnd_1057925 := by
    simpa [prefixWord, tailWord_1057925, baseEnd_1057925] using wordTrace_append hprefix tailTrace_1057925
  have hstable : (prefixWord ++ tailWord_1057925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057925).length < 2 ^ (prefixWord ++ tailWord_1057925).sum := by decide
  have hdescent : baseEnd_1057925 < baseStart_1057925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057936 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 1, 9]
def baseStart_1057936 : Nat := 118140960795 + 1057936 * 2 ^ 59
def prefixEnd_1057936 : Nat := 4983230072969 + 3 ^ 40 * 1057936 * 2
def baseEnd_1057936 : Nat := 362153113130052036156431

theorem tailTrace_1057936 : CollatzResearch.WordTrace tailWord_1057936 prefixEnd_1057936 362153113130052036156431 := by
  unfold tailWord_1057936
  simp only [CollatzResearch.WordTrace]
  refine ⟨19293047947643013964576831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25724063930190685286102441 19293047947643013964576831)
  ·
    refine ⟨28939571921464520946865247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19293047947643013964576831 28939571921464520946865247)
    ·
      refine ⟨43409357882196781420297871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28939571921464520946865247 43409357882196781420297871)
      ·
        refine ⟨65114036823295172130446807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43409357882196781420297871 65114036823295172130446807)
        ·
          refine ⟨97671055234942758195670211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65114036823295172130446807 97671055234942758195670211)
          ·
            refine ⟨146506582852414137293505317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97671055234942758195670211 146506582852414137293505317)
            ·
              refine ⟨27469984284827650742532247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 146506582852414137293505317 27469984284827650742532247)
              ·
                refine ⟨41204976427241476113798371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27469984284827650742532247 41204976427241476113798371)
                ·
                  refine ⟨61807464640862214170697557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41204976427241476113798371 61807464640862214170697557)
                  ·
                    refine ⟨362153113130052036156431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 61807464640862214170697557 362153113130052036156431)
                    ·
                      rfl

theorem cell22_1057936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 1, 9].length) (baseStart_1057936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1057936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1057936 prefixEnd_1057936 := by exact prefixLift 1057936
  have htrace : WordTrace (prefixWord ++ tailWord_1057936) baseStart_1057936 baseEnd_1057936 := by
    simpa [prefixWord, tailWord_1057936, baseEnd_1057936] using wordTrace_append hprefix tailTrace_1057936
  have hstable : (prefixWord ++ tailWord_1057936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057936).length < 2 ^ (prefixWord ++ tailWord_1057936).sum := by decide
  have hdescent : baseEnd_1057936 < baseStart_1057936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057959 : List Nat := [1, 1, 6, 2, 1, 3, 1, 2, 2, 3]
def baseStart_1057959 : Nat := 118140960795 + 1057959 * 2 ^ 59
def prefixEnd_1057959 : Nat := 4983230072969 + 3 ^ 40 * 1057959 * 2
def baseEnd_1057959 : Nat := 362160986500087642831361

theorem tailTrace_1057959 : CollatzResearch.WordTrace tailWord_1057959 prefixEnd_1057959 362160986500087642831361 := by
  unfold tailWord_1057959
  simp only [CollatzResearch.WordTrace]
  refine ⟨38586934774202702857240931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25724623182801801904827287 38586934774202702857240931)
  ·
    refine ⟨57880402161304054285861397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38586934774202702857240931 57880402161304054285861397)
    ·
      refine ⟨2713143851311127544649753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 57880402161304054285861397 2713143851311127544649753)
      ·
        refine ⟨2034857888483345658487315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2713143851311127544649753 2034857888483345658487315)
        ·
          refine ⟨3052286832725018487730973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2034857888483345658487315 3052286832725018487730973)
          ·
            refine ⟨1144607562271881932899115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3052286832725018487730973 1144607562271881932899115)
            ·
              refine ⟨1716911343407822899348673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1144607562271881932899115 1716911343407822899348673)
              ·
                refine ⟨1287683507555867174511505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1716911343407822899348673 1287683507555867174511505)
                ·
                  refine ⟨965762630666900380883629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1287683507555867174511505 965762630666900380883629)
                  ·
                    refine ⟨362160986500087642831361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 965762630666900380883629 362160986500087642831361)
                    ·
                      rfl

theorem cell22_1057959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_1057959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1057959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1057959 prefixEnd_1057959 := by exact prefixLift 1057959
  have htrace : WordTrace (prefixWord ++ tailWord_1057959) baseStart_1057959 baseEnd_1057959 := by
    simpa [prefixWord, tailWord_1057959, baseEnd_1057959] using wordTrace_append hprefix tailTrace_1057959
  have hstable : (prefixWord ++ tailWord_1057959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057959).length < 2 ^ (prefixWord ++ tailWord_1057959).sum := by decide
  have hdescent : baseEnd_1057959 < baseStart_1057959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057970 : List Nat := [3, 2, 1, 1, 1, 4, 1, 3, 3, 3]
def baseStart_1057970 : Nat := 118140960795 + 1057970 * 2 ^ 59
def prefixEnd_1057970 : Nat := 4983230072969 + 3 ^ 40 * 1057970 * 2
def baseEnd_1057970 : Nat := 362164752024887280806327

theorem tailTrace_1057970 : CollatzResearch.WordTrace tailWord_1057970 prefixEnd_1057970 362164752024887280806327 := by
  unfold tailWord_1057970
  simp only [CollatzResearch.WordTrace]
  refine ⟨9646833994290712933972841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25724890651441901157260909 9646833994290712933972841)
  ·
    refine ⟨7235125495718034700479631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9646833994290712933972841 7235125495718034700479631)
    ·
      refine ⟨10852688243577052050719447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7235125495718034700479631 10852688243577052050719447)
      ·
        refine ⟨16279032365365578076079171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10852688243577052050719447 16279032365365578076079171)
        ·
          refine ⟨24418548548048367114118757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16279032365365578076079171 24418548548048367114118757)
          ·
            refine ⟨4578477852759068833897267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24418548548048367114118757 4578477852759068833897267)
            ·
              refine ⟨6867716779138603250845901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4578477852759068833897267 6867716779138603250845901)
              ·
                refine ⟨2575393792176976219067213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6867716779138603250845901 2575393792176976219067213)
                ·
                  refine ⟨965772672066366082150205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2575393792176976219067213 965772672066366082150205)
                  ·
                    refine ⟨362164752024887280806327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 965772672066366082150205 362164752024887280806327)
                    ·
                      rfl

theorem cell22_1057970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 3, 3].length) (baseStart_1057970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1057970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1057970 prefixEnd_1057970 := by exact prefixLift 1057970
  have htrace : WordTrace (prefixWord ++ tailWord_1057970) baseStart_1057970 baseEnd_1057970 := by
    simpa [prefixWord, tailWord_1057970, baseEnd_1057970] using wordTrace_append hprefix tailTrace_1057970
  have hstable : (prefixWord ++ tailWord_1057970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057970).length < 2 ^ (prefixWord ++ tailWord_1057970).sum := by decide
  have hdescent : baseEnd_1057970 < baseStart_1057970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057983 : List Nat := [1, 1, 2, 2, 2, 2, 2, 5, 5]
def baseStart_1057983 : Nat := 118140960795 + 1057983 * 2 ^ 59
def prefixEnd_1057983 : Nat := 4983230072969 + 3 ^ 40 * 1057983 * 2
def baseEnd_1057983 : Nat := 120723067396853193410429

theorem tailTrace_1057983 : CollatzResearch.WordTrace tailWord_1057983 prefixEnd_1057983 120723067396853193410429 := by
  unfold tailWord_1057983
  simp only [CollatzResearch.WordTrace]
  refine ⟨38587810126115754956114603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25725206750743836637409735 38587810126115754956114603)
  ·
    refine ⟨57881715189173632434171905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38587810126115754956114603 57881715189173632434171905)
    ·
      refine ⟨43411286391880224325628929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57881715189173632434171905 43411286391880224325628929)
      ·
        refine ⟨32558464793910168244221697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43411286391880224325628929 32558464793910168244221697)
        ·
          refine ⟨24418848595432626183166273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32558464793910168244221697 24418848595432626183166273)
          ·
            refine ⟨18314136446574469637374705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24418848595432626183166273 18314136446574469637374705)
            ·
              refine ⟨13735602334930852228031029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18314136446574469637374705 13735602334930852228031029)
              ·
                refine ⟨1287712718899767396377909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13735602334930852228031029 1287712718899767396377909)
                ·
                  refine ⟨120723067396853193410429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1287712718899767396377909 120723067396853193410429)
                  ·
                    rfl

theorem cell22_1057983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 5, 5].length) (baseStart_1057983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1057983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1057983 prefixEnd_1057983 := by exact prefixLift 1057983
  have htrace : WordTrace (prefixWord ++ tailWord_1057983) baseStart_1057983 baseEnd_1057983 := by
    simpa [prefixWord, tailWord_1057983, baseEnd_1057983] using wordTrace_append hprefix tailTrace_1057983
  have hstable : (prefixWord ++ tailWord_1057983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057983).length < 2 ^ (prefixWord ++ tailWord_1057983).sum := by decide
  have hdescent : baseEnd_1057983 < baseStart_1057983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058021 : List Nat := [1, 3, 1, 4, 3, 1, 3, 2, 1, 3]
def baseStart_1058021 : Nat := 118140960795 + 1058021 * 2 ^ 59
def prefixEnd_1058021 : Nat := 4983230072969 + 3 ^ 40 * 1058021 * 2
def baseEnd_1058021 : Nat := 362182210367140147781171

theorem tailTrace_1058021 : CollatzResearch.WordTrace tailWord_1058021 prefixEnd_1058021 362182210367140147781171 := by
  unfold tailWord_1058021
  simp only [CollatzResearch.WordTrace]
  refine ⟨38589196099978087445997917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25726130733318724963998611 38589196099978087445997917)
  ·
    refine ⟨14470948537491782792249219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38589196099978087445997917 14470948537491782792249219)
    ·
      refine ⟨21706422806237674188373829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14470948537491782792249219 21706422806237674188373829)
      ·
        refine ⟨4069954276169563910320093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21706422806237674188373829 4069954276169563910320093)
        ·
          refine ⟨1526232853563586466370035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4069954276169563910320093 1526232853563586466370035)
          ·
            refine ⟨2289349280345379699555053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1526232853563586466370035 2289349280345379699555053)
            ·
              refine ⟨858505980129517387333145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2289349280345379699555053 858505980129517387333145)
              ·
                refine ⟨643879485097138040499859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 858505980129517387333145 643879485097138040499859)
                ·
                  refine ⟨965819227645707060749789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 643879485097138040499859 965819227645707060749789)
                  ·
                    refine ⟨362182210367140147781171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 965819227645707060749789 362182210367140147781171)
                    ·
                      rfl

theorem cell22_1058021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 2, 1, 3].length) (baseStart_1058021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1058021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1058021 prefixEnd_1058021 := by exact prefixLift 1058021
  have htrace : WordTrace (prefixWord ++ tailWord_1058021) baseStart_1058021 baseEnd_1058021 := by
    simpa [prefixWord, tailWord_1058021, baseEnd_1058021] using wordTrace_append hprefix tailTrace_1058021
  have hstable : (prefixWord ++ tailWord_1058021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058021).length < 2 ^ (prefixWord ++ tailWord_1058021).sum := by decide
  have hdescent : baseEnd_1058021 < baseStart_1058021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058034 : List Nat := [3, 2, 1, 3, 3, 2, 2, 1, 5]
def baseStart_1058034 : Nat := 118140960795 + 1058034 * 2 ^ 59
def prefixEnd_1058034 : Nat := 4983230072969 + 3 ^ 40 * 1058034 * 2
def baseEnd_1058034 : Nat := 120728886844270815735377

theorem tailTrace_1058034 : CollatzResearch.WordTrace tailWord_1058034 prefixEnd_1058034 120728886844270815735377 := by
  unfold tailWord_1058034
  simp only [CollatzResearch.WordTrace]
  refine ⟨9647417562232747666555289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25726446832620660444147437 9647417562232747666555289)
  ·
    refine ⟨7235563171674560749916467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9647417562232747666555289 7235563171674560749916467)
    ·
      refine ⟨10853344757511841124874701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7235563171674560749916467 10853344757511841124874701)
      ·
        refine ⟨4070004284066940421828013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10853344757511841124874701 4070004284066940421828013)
        ·
          refine ⟨1526251606525102658185505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4070004284066940421828013 1526251606525102658185505)
          ·
            refine ⟨1144688704893826993639129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1526251606525102658185505 1144688704893826993639129)
            ·
              refine ⟨858516528670370245229347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1144688704893826993639129 858516528670370245229347)
              ·
                refine ⟨1287774793005555367844021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 858516528670370245229347 1287774793005555367844021)
                ·
                  refine ⟨120728886844270815735377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1287774793005555367844021 120728886844270815735377)
                  ·
                    rfl

theorem cell22_1058034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 1, 5].length) (baseStart_1058034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1058034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1058034 prefixEnd_1058034 := by exact prefixLift 1058034
  have htrace : WordTrace (prefixWord ++ tailWord_1058034) baseStart_1058034 baseEnd_1058034 := by
    simpa [prefixWord, tailWord_1058034, baseEnd_1058034] using wordTrace_append hprefix tailTrace_1058034
  have hstable : (prefixWord ++ tailWord_1058034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058034).length < 2 ^ (prefixWord ++ tailWord_1058034).sum := by decide
  have hdescent : baseEnd_1058034 < baseStart_1058034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058047 : List Nat := [1, 1, 2, 2, 1, 7, 1, 2, 1, 4]
def baseStart_1058047 : Nat := 118140960795 + 1058047 * 2 ^ 59
def prefixEnd_1058047 : Nat := 4983230072969 + 3 ^ 40 * 1058047 * 2
def baseEnd_1058047 : Nat := 362191110698484746631091

theorem tailTrace_1058047 : CollatzResearch.WordTrace tailWord_1058047 prefixEnd_1058047 362191110698484746631091 := by
  unfold tailWord_1058047
  simp only [CollatzResearch.WordTrace]
  refine ⟨38590144397883893886444395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25726762931922595924296263 38590144397883893886444395)
  ·
    refine ⟨57885216596825840829666593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38590144397883893886444395 57885216596825840829666593)
    ·
      refine ⟨43413912447619380622249945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57885216596825840829666593 43413912447619380622249945)
      ·
        refine ⟨32560434335714535466687459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43413912447619380622249945 32560434335714535466687459)
        ·
          refine ⟨48840651503571803200031189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32560434335714535466687459 48840651503571803200031189)
          ·
            refine ⟨1144702769614964137500731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 48840651503571803200031189 1144702769614964137500731)
            ·
              refine ⟨1717054154422446206251097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1144702769614964137500731 1717054154422446206251097)
              ·
                refine ⟨1287790615816834654688323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1717054154422446206251097 1287790615816834654688323)
                ·
                  refine ⟨1931685923725251982032485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1287790615816834654688323 1931685923725251982032485)
                  ·
                    refine ⟨362191110698484746631091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1931685923725251982032485 362191110698484746631091)
                    ·
                      rfl

theorem cell22_1058047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 2, 1, 4].length) (baseStart_1058047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1058047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1058047 prefixEnd_1058047 := by exact prefixLift 1058047
  have htrace : WordTrace (prefixWord ++ tailWord_1058047) baseStart_1058047 baseEnd_1058047 := by
    simpa [prefixWord, tailWord_1058047, baseEnd_1058047] using wordTrace_append hprefix tailTrace_1058047
  have hstable : (prefixWord ++ tailWord_1058047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058047).length < 2 ^ (prefixWord ++ tailWord_1058047).sum := by decide
  have hdescent : baseEnd_1058047 < baseStart_1058047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058060 : List Nat := [2, 2, 1, 2, 2, 4, 1, 2, 1, 5]
def baseStart_1058060 : Nat := 118140960795 + 1058060 * 2 ^ 59
def prefixEnd_1058060 : Nat := 4983230072969 + 3 ^ 40 * 1058060 * 2
def baseEnd_1058060 : Nat := 362195560864157046056051

theorem tailTrace_1058060 : CollatzResearch.WordTrace tailWord_1058060 prefixEnd_1058060 362195560864157046056051 := by
  unfold tailWord_1058060
  simp only [CollatzResearch.WordTrace]
  refine ⟨19295309273418398553333817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25727079031224531404445089 19295309273418398553333817)
  ·
    refine ⟨14471481955063798915000363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19295309273418398553333817 14471481955063798915000363)
    ·
      refine ⟨21707222932595698372500545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14471481955063798915000363 21707222932595698372500545)
      ·
        refine ⟨16280417199446773779375409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21707222932595698372500545 16280417199446773779375409)
        ·
          refine ⟨12210312899585080334531557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16280417199446773779375409 12210312899585080334531557)
          ·
            refine ⟨2289433668672202562724667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12210312899585080334531557 2289433668672202562724667)
            ·
              refine ⟨3434150503008303844087001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2289433668672202562724667 3434150503008303844087001)
              ·
                refine ⟨2575612877256227883065251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3434150503008303844087001 2575612877256227883065251)
                ·
                  refine ⟨3863419315884341824597877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2575612877256227883065251 3863419315884341824597877)
                  ·
                    refine ⟨362195560864157046056051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3863419315884341824597877 362195560864157046056051)
                    ·
                      rfl

theorem cell22_1058060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 1, 5].length) (baseStart_1058060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1058060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1058060 prefixEnd_1058060 := by exact prefixLift 1058060
  have htrace : WordTrace (prefixWord ++ tailWord_1058060) baseStart_1058060 baseEnd_1058060 := by
    simpa [prefixWord, tailWord_1058060, baseEnd_1058060] using wordTrace_append hprefix tailTrace_1058060
  have hstable : (prefixWord ++ tailWord_1058060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058060).length < 2 ^ (prefixWord ++ tailWord_1058060).sum := by decide
  have hdescent : baseEnd_1058060 < baseStart_1058060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058135 : List Nat := [1, 1, 3, 2, 3, 3, 1, 1, 7]
def baseStart_1058135 : Nat := 118140960795 + 1058135 * 2 ^ 59
def prefixEnd_1058135 : Nat := 4983230072969 + 3 ^ 40 * 1058135 * 2
def baseEnd_1058135 : Nat := 120740411632293950143607

theorem tailTrace_1058135 : CollatzResearch.WordTrace tailWord_1058135 prefixEnd_1058135 120740411632293950143607 := by
  unfold tailWord_1058135
  simp only [CollatzResearch.WordTrace]
  refine ⟨38593354021565084915647859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25728902681043389943765239 38593354021565084915647859)
  ·
    refine ⟨57890031032347627373471789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38593354021565084915647859 57890031032347627373471789)
    ·
      refine ⟨21708761637130360265051921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57890031032347627373471789 21708761637130360265051921)
      ·
        refine ⟨16281571227847770198788941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21708761637130360265051921 16281571227847770198788941)
        ·
          refine ⟨6105589210442913824545853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16281571227847770198788941 6105589210442913824545853)
          ·
            refine ⟨2289595953916092684204695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6105589210442913824545853 2289595953916092684204695)
            ·
              refine ⟨3434393930874139026307043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2289595953916092684204695 3434393930874139026307043)
              ·
                refine ⟨5151590896311208539460565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3434393930874139026307043 5151590896311208539460565)
                ·
                  refine ⟨120740411632293950143607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5151590896311208539460565 120740411632293950143607)
                  ·
                    rfl

theorem cell22_1058135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 7].length) (baseStart_1058135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1058135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1058135 prefixEnd_1058135 := by exact prefixLift 1058135
  have htrace : WordTrace (prefixWord ++ tailWord_1058135) baseStart_1058135 baseEnd_1058135 := by
    simpa [prefixWord, tailWord_1058135, baseEnd_1058135] using wordTrace_append hprefix tailTrace_1058135
  have hstable : (prefixWord ++ tailWord_1058135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058135).length < 2 ^ (prefixWord ++ tailWord_1058135).sum := by decide
  have hdescent : baseEnd_1058135 < baseStart_1058135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058197 : List Nat := [1, 3, 2, 1, 1, 2, 2, 6, 4]
def baseStart_1058197 : Nat := 118140960795 + 1058197 * 2 ^ 59
def prefixEnd_1058197 : Nat := 4983230072969 + 3 ^ 40 * 1058197 * 2
def baseEnd_1058197 : Nat := 120747486254644785126877

theorem tailTrace_1058197 : CollatzResearch.WordTrace tailWord_1058197 prefixEnd_1058197 120747486254644785126877 := by
  unfold tailWord_1058197
  simp only [CollatzResearch.WordTrace]
  refine ⟨38595615347340469504404845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25730410231560313002936563 38595615347340469504404845)
  ·
    refine ⟨14473355755252676064151817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38595615347340469504404845 14473355755252676064151817)
    ·
      refine ⟨10855016816439507048113863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14473355755252676064151817 10855016816439507048113863)
      ·
        refine ⟨16282525224659260572170795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10855016816439507048113863 16282525224659260572170795)
        ·
          refine ⟨24423787836988890858256193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16282525224659260572170795 24423787836988890858256193)
          ·
            refine ⟨18317840877741668143692145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24423787836988890858256193 18317840877741668143692145)
            ·
              refine ⟨13738380658306251107769109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18317840877741668143692145 13738380658306251107769109)
              ·
                refine ⟨643986593358105520676677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13738380658306251107769109 643986593358105520676677)
                ·
                  refine ⟨120747486254644785126877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 643986593358105520676677 120747486254644785126877)
                  ·
                    rfl

theorem cell22_1058197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 6, 4].length) (baseStart_1058197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1058197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1058197 prefixEnd_1058197 := by exact prefixLift 1058197
  have htrace : WordTrace (prefixWord ++ tailWord_1058197) baseStart_1058197 baseEnd_1058197 := by
    simpa [prefixWord, tailWord_1058197, baseEnd_1058197] using wordTrace_append hprefix tailTrace_1058197
  have hstable : (prefixWord ++ tailWord_1058197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058197).length < 2 ^ (prefixWord ++ tailWord_1058197).sum := by decide
  have hdescent : baseEnd_1058197 < baseStart_1058197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058225 : List Nat := [1, 2, 2, 4, 1, 1, 1, 10]
def baseStart_1058225 : Nat := 118140960795 + 1058225 * 2 ^ 59
def prefixEnd_1058225 : Nat := 4983230072969 + 3 ^ 40 * 1058225 * 2
def baseEnd_1058225 : Nat := 40250227081794623964505

theorem tailTrace_1058225 : CollatzResearch.WordTrace tailWord_1058225 prefixEnd_1058225 40250227081794623964505 := by
  unfold tailWord_1058225
  simp only [CollatzResearch.WordTrace]
  refine ⟨38596636591239030286424129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25731091060826020190949419 38596636591239030286424129)
  ·
    refine ⟨28947477443429272714818097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38596636591239030286424129 28947477443429272714818097)
    ·
      refine ⟨21710608082571954536113573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28947477443429272714818097 21710608082571954536113573)
      ·
        refine ⟨4070739015482241475521295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21710608082571954536113573 4070739015482241475521295)
        ·
          refine ⟨6106108523223362213281943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4070739015482241475521295 6106108523223362213281943)
          ·
            refine ⟨9159162784835043319922915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6106108523223362213281943 9159162784835043319922915)
            ·
              refine ⟨13738744177252564979884373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9159162784835043319922915 13738744177252564979884373)
              ·
                refine ⟨40250227081794623964505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 13738744177252564979884373 40250227081794623964505)
                ·
                  rfl

theorem cell22_1058225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 10].length) (baseStart_1058225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1058225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1058225 prefixEnd_1058225 := by exact prefixLift 1058225
  have htrace : WordTrace (prefixWord ++ tailWord_1058225) baseStart_1058225 baseEnd_1058225 := by
    simpa [prefixWord, tailWord_1058225, baseEnd_1058225] using wordTrace_append hprefix tailTrace_1058225
  have hstable : (prefixWord ++ tailWord_1058225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058225).length < 2 ^ (prefixWord ++ tailWord_1058225).sum := by decide
  have hdescent : baseEnd_1058225 < baseStart_1058225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058244 : List Nat := [2, 3, 3, 2, 1, 1, 2, 2, 2, 4]
def baseStart_1058244 : Nat := 118140960795 + 1058244 * 2 ^ 59
def prefixEnd_1058244 : Nat := 4983230072969 + 3 ^ 40 * 1058244 * 2
def baseEnd_1058244 : Nat := 362258547824441899455487

theorem tailTrace_1058244 : CollatzResearch.WordTrace tailWord_1058244 prefixEnd_1058244 362258547824441899455487 := by
  unfold tailWord_1058244
  simp only [CollatzResearch.WordTrace]
  refine ⟨19298664789085098265682893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25731553052113464354243857 19298664789085098265682893)
  ·
    refine ⟨7236999295906911849631085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19298664789085098265682893 7236999295906911849631085)
    ·
      refine ⟨2713874735965091943611657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7236999295906911849631085 2713874735965091943611657)
      ·
        refine ⟨2035406051973818957708743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2713874735965091943611657 2035406051973818957708743)
        ·
          refine ⟨3053109077960728436563115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2035406051973818957708743 3053109077960728436563115)
          ·
            refine ⟨4579663616941092654844673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3053109077960728436563115 4579663616941092654844673)
            ·
              refine ⟨3434747712705819491133505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4579663616941092654844673 3434747712705819491133505)
              ·
                refine ⟨2576060784529364618350129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3434747712705819491133505 2576060784529364618350129)
                ·
                  refine ⟨1932045588397023463762597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2576060784529364618350129 1932045588397023463762597)
                  ·
                    refine ⟨362258547824441899455487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1932045588397023463762597 362258547824441899455487)
                    ·
                      rfl

theorem cell22_1058244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_1058244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1058244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1058244 prefixEnd_1058244 := by exact prefixLift 1058244
  have htrace : WordTrace (prefixWord ++ tailWord_1058244) baseStart_1058244 baseEnd_1058244 := by
    simpa [prefixWord, tailWord_1058244, baseEnd_1058244] using wordTrace_append hprefix tailTrace_1058244
  have hstable : (prefixWord ++ tailWord_1058244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058244).length < 2 ^ (prefixWord ++ tailWord_1058244).sum := by decide
  have hdescent : baseEnd_1058244 < baseStart_1058244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058255 : List Nat := [1, 1, 2, 1, 1, 4, 3, 1, 2, 6]
def baseStart_1058255 : Nat := 118140960795 + 1058255 * 2 ^ 59
def prefixEnd_1058255 : Nat := 4983230072969 + 3 ^ 40 * 1058255 * 2
def baseEnd_1058255 : Nat := 362262313349241537430453

theorem tailTrace_1058255 : CollatzResearch.WordTrace tailWord_1058255 prefixEnd_1058255 362262313349241537430453 := by
  unfold tailWord_1058255
  simp only [CollatzResearch.WordTrace]
  refine ⟨38597730781130345410016219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25731820520753563606677479 38597730781130345410016219)
  ·
    refine ⟨57896596171695518115024329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38597730781130345410016219 57896596171695518115024329)
    ·
      refine ⟨43422447128771638586268247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57896596171695518115024329 43422447128771638586268247)
      ·
        refine ⟨65133670693157457879402371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43422447128771638586268247 65133670693157457879402371)
        ·
          refine ⟨97700506039736186819103557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65133670693157457879402371 97700506039736186819103557)
          ·
            refine ⟨18318844882450535028581917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97700506039736186819103557 18318844882450535028581917)
            ·
              refine ⟨6869566830918950635718219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18318844882450535028581917 6869566830918950635718219)
              ·
                refine ⟨10304350246378425953577329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6869566830918950635718219 10304350246378425953577329)
                ·
                  refine ⟨7728262684783819465182997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10304350246378425953577329 7728262684783819465182997)
                  ·
                    refine ⟨362262313349241537430453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7728262684783819465182997 362262313349241537430453)
                    ·
                      rfl

theorem cell22_1058255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 6].length) (baseStart_1058255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1058255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1058255 prefixEnd_1058255 := by exact prefixLift 1058255
  have htrace : WordTrace (prefixWord ++ tailWord_1058255) baseStart_1058255 baseEnd_1058255 := by
    simpa [prefixWord, tailWord_1058255, baseEnd_1058255] using wordTrace_append hprefix tailTrace_1058255
  have hstable : (prefixWord ++ tailWord_1058255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058255).length < 2 ^ (prefixWord ++ tailWord_1058255).sum := by decide
  have hdescent : baseEnd_1058255 < baseStart_1058255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058332 : List Nat := [2, 2, 3, 1, 2, 1, 1, 4, 6]
def baseStart_1058332 : Nat := 118140960795 + 1058332 * 2 ^ 59
def prefixEnd_1058332 : Nat := 4983230072969 + 3 ^ 40 * 1058332 * 2
def baseEnd_1058332 : Nat := 120762890674279667751739

theorem tailTrace_1058332 : CollatzResearch.WordTrace tailWord_1058332 prefixEnd_1058332 120762890674279667751739 := by
  unfold tailWord_1058332
  simp only [CollatzResearch.WordTrace]
  refine ⟨19300269600925693780284625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25733692801234258373712833 19300269600925693780284625)
  ·
    refine ⟨14475202200694270335213469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19300269600925693780284625 14475202200694270335213469)
    ·
      refine ⟨5428200825260351375705051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14475202200694270335213469 5428200825260351375705051)
      ·
        refine ⟨8142301237890527063557577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5428200825260351375705051 8142301237890527063557577)
        ·
          refine ⟨6106725928417895297668183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8142301237890527063557577 6106725928417895297668183)
          ·
            refine ⟨9160088892626842946502275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6106725928417895297668183 9160088892626842946502275)
            ·
              refine ⟨13740133338940264419753413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9160088892626842946502275 13740133338940264419753413)
              ·
                refine ⟨2576275001051299578703765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13740133338940264419753413 2576275001051299578703765)
                ·
                  refine ⟨120762890674279667751739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2576275001051299578703765 120762890674279667751739)
                  ·
                    rfl

theorem cell22_1058332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 6].length) (baseStart_1058332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1058332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1058332 prefixEnd_1058332 := by exact prefixLift 1058332
  have htrace : WordTrace (prefixWord ++ tailWord_1058332) baseStart_1058332 baseEnd_1058332 := by
    simpa [prefixWord, tailWord_1058332, baseEnd_1058332] using wordTrace_append hprefix tailTrace_1058332
  have hstable : (prefixWord ++ tailWord_1058332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058332).length < 2 ^ (prefixWord ++ tailWord_1058332).sum := by decide
  have hdescent : baseEnd_1058332 < baseStart_1058332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058396 : List Nat := [2, 2, 4, 1, 2, 2, 2, 1, 2, 4]
def baseStart_1058396 : Nat := 118140960795 + 1058396 * 2 ^ 59
def prefixEnd_1058396 : Nat := 4983230072969 + 3 ^ 40 * 1058396 * 2
def baseEnd_1058396 : Nat := 362310580530764169655021

theorem tailTrace_1058396 : CollatzResearch.WordTrace tailWord_1058396 prefixEnd_1058396 362310580530764169655021 := by
  unfold tailWord_1058396
  simp only [CollatzResearch.WordTrace]
  refine ⟨19301436736809763245449521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25735248982413017660599361 19301436736809763245449521)
  ·
    refine ⟨14476077552607322434087141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19301436736809763245449521 14476077552607322434087141)
    ·
      refine ⟨2714264541113872956391339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14476077552607322434087141 2714264541113872956391339)
      ·
        refine ⟨4071396811670809434587009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2714264541113872956391339 4071396811670809434587009)
        ·
          refine ⟨3053547608753107075940257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4071396811670809434587009 3053547608753107075940257)
          ·
            refine ⟨2290160706564830306955193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3053547608753107075940257 2290160706564830306955193)
            ·
              refine ⟨1717620529923622730216395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2290160706564830306955193 1717620529923622730216395)
              ·
                refine ⟨2576430794885434095324593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1717620529923622730216395 2576430794885434095324593)
                ·
                  refine ⟨1932323096164075571493445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2576430794885434095324593 1932323096164075571493445)
                  ·
                    refine ⟨362310580530764169655021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1932323096164075571493445 362310580530764169655021)
                    ·
                      rfl

theorem cell22_1058396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_1058396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1058396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1058396 prefixEnd_1058396 := by exact prefixLift 1058396
  have htrace : WordTrace (prefixWord ++ tailWord_1058396) baseStart_1058396 baseEnd_1058396 := by
    simpa [prefixWord, tailWord_1058396, baseEnd_1058396] using wordTrace_append hprefix tailTrace_1058396
  have hstable : (prefixWord ++ tailWord_1058396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058396).length < 2 ^ (prefixWord ++ tailWord_1058396).sum := by decide
  have hdescent : baseEnd_1058396 < baseStart_1058396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058439 : List Nat := [1, 1, 4, 2, 1, 3, 2, 3, 5]
def baseStart_1058439 : Nat := 118140960795 + 1058439 * 2 ^ 59
def prefixEnd_1058439 : Nat := 4983230072969 + 3 ^ 40 * 1058439 * 2
def baseEnd_1058439 : Nat := 120775100103175463609963

theorem tailTrace_1058439 : CollatzResearch.WordTrace tailWord_1058439 prefixEnd_1058439 120775100103175463609963 := by
  unfold tailWord_1058439
  simp only [CollatzResearch.WordTrace]
  refine ⟨38604441812463744834714371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25736294541642496556476247 38604441812463744834714371)
  ·
    refine ⟨57906662718695617252071557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38604441812463744834714371 57906662718695617252071557)
    ·
      refine ⟨10857499259755428234763417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57906662718695617252071557 10857499259755428234763417)
      ·
        refine ⟨8143124444816571176072563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10857499259755428234763417 8143124444816571176072563)
        ·
          refine ⟨12214686667224856764108845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8143124444816571176072563 12214686667224856764108845)
          ·
            refine ⟨4580507500209321286540817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12214686667224856764108845 4580507500209321286540817)
            ·
              refine ⟨3435380625156990964905613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4580507500209321286540817 3435380625156990964905613)
              ·
                refine ⟨1288267734433871611839605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3435380625156990964905613 1288267734433871611839605)
                ·
                  refine ⟨120775100103175463609963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1288267734433871611839605 120775100103175463609963)
                  ·
                    rfl

theorem cell22_1058439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 3, 5].length) (baseStart_1058439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1058439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1058439 prefixEnd_1058439 := by exact prefixLift 1058439
  have htrace : WordTrace (prefixWord ++ tailWord_1058439) baseStart_1058439 baseEnd_1058439 := by
    simpa [prefixWord, tailWord_1058439, baseEnd_1058439] using wordTrace_append hprefix tailTrace_1058439
  have hstable : (prefixWord ++ tailWord_1058439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058439).length < 2 ^ (prefixWord ++ tailWord_1058439).sum := by decide
  have hdescent : baseEnd_1058439 < baseStart_1058439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058460 : List Nat := [2, 2, 3, 2, 3, 1, 2, 3, 1, 3]
def baseStart_1058460 : Nat := 118140960795 + 1058460 * 2 ^ 59
def prefixEnd_1058460 : Nat := 4983230072969 + 3 ^ 40 * 1058460 * 2
def baseEnd_1058460 : Nat := 362332489038689336054825

theorem tailTrace_1058460 : CollatzResearch.WordTrace tailWord_1058460 prefixEnd_1058460 362332489038689336054825 := by
  unfold tailWord_1058460
  simp only [CollatzResearch.WordTrace]
  refine ⟨19302603872693832710614417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25736805163591776947485889 19302603872693832710614417)
  ·
    refine ⟨14476952904520374532960813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19302603872693832710614417 14476952904520374532960813)
    ·
      refine ⟨5428857339195140449860305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14476952904520374532960813 5428857339195140449860305)
      ·
        refine ⟨4071643004396355337395229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5428857339195140449860305 4071643004396355337395229)
        ·
          refine ⟨1526866126648633251523211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4071643004396355337395229 1526866126648633251523211)
          ·
            refine ⟨2290299189972949877284817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1526866126648633251523211 2290299189972949877284817)
            ·
              refine ⟨1717724392479712407963613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2290299189972949877284817 1717724392479712407963613)
              ·
                refine ⟨644146647179892152986355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1717724392479712407963613 644146647179892152986355)
                ·
                  refine ⟨966219970769838229479533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 644146647179892152986355 966219970769838229479533)
                  ·
                    refine ⟨362332489038689336054825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 966219970769838229479533 362332489038689336054825)
                    ·
                      rfl

theorem cell22_1058460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_1058460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1058460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1058460 prefixEnd_1058460 := by exact prefixLift 1058460
  have htrace : WordTrace (prefixWord ++ tailWord_1058460) baseStart_1058460 baseEnd_1058460 := by
    simpa [prefixWord, tailWord_1058460, baseEnd_1058460] using wordTrace_append hprefix tailTrace_1058460
  have hstable : (prefixWord ++ tailWord_1058460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058460).length < 2 ^ (prefixWord ++ tailWord_1058460).sum := by decide
  have hdescent : baseEnd_1058460 < baseStart_1058460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058467 : List Nat := [1, 1, 1, 4, 1, 1, 3, 2, 8]
def baseStart_1058467 : Nat := 118140960795 + 1058467 * 2 ^ 59
def prefixEnd_1058467 : Nat := 4983230072969 + 3 ^ 40 * 1058467 * 2
def baseEnd_1058467 : Nat := 120778295093914550376601

theorem tailTrace_1058467 : CollatzResearch.WordTrace tailWord_1058467 prefixEnd_1058467 120778295093914550376601 := by
  unfold tailWord_1058467
  simp only [CollatzResearch.WordTrace]
  refine ⟨38605463056362305616733655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25736975370908203744489103 38605463056362305616733655)
  ·
    refine ⟨57908194584543458425100483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38605463056362305616733655 57908194584543458425100483)
    ·
      refine ⟨86862291876815187637650725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57908194584543458425100483 86862291876815187637650725)
      ·
        refine ⟨16286679726902847682059511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86862291876815187637650725 16286679726902847682059511)
        ·
          refine ⟨24430019590354271523089267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16286679726902847682059511 24430019590354271523089267)
          ·
            refine ⟨36645029385531407284633901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24430019590354271523089267 36645029385531407284633901)
            ·
              refine ⟨13741886019574277731737713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36645029385531407284633901 13741886019574277731737713)
              ·
                refine ⟨10306414514680708298803285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13741886019574277731737713 10306414514680708298803285)
                ·
                  refine ⟨120778295093914550376601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10306414514680708298803285 120778295093914550376601)
                  ·
                    rfl

theorem cell22_1058467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 8].length) (baseStart_1058467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1058467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1058467 prefixEnd_1058467 := by exact prefixLift 1058467
  have htrace : WordTrace (prefixWord ++ tailWord_1058467) baseStart_1058467 baseEnd_1058467 := by
    simpa [prefixWord, tailWord_1058467, baseEnd_1058467] using wordTrace_append hprefix tailTrace_1058467
  have hstable : (prefixWord ++ tailWord_1058467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058467).length < 2 ^ (prefixWord ++ tailWord_1058467).sum := by decide
  have hdescent : baseEnd_1058467 < baseStart_1058467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058535 : List Nat := [1, 1, 5, 4, 2, 1, 1, 1, 6]
def baseStart_1058535 : Nat := 118140960795 + 1058535 * 2 ^ 59
def prefixEnd_1058535 : Nat := 4983230072969 + 3 ^ 40 * 1058535 * 2
def baseEnd_1058535 : Nat := 120786054357138046809865

theorem tailTrace_1058535 : CollatzResearch.WordTrace tailWord_1058535 prefixEnd_1058535 120786054357138046809865 := by
  unfold tailWord_1058535
  simp only [CollatzResearch.WordTrace]
  refine ⟨38607943220115953230209059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25738628813410635486806039 38607943220115953230209059)
  ·
    refine ⟨57911914830173929845313589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38607943220115953230209059 57911914830173929845313589)
    ·
      refine ⟨5429242015328805922998149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57911914830173929845313589 5429242015328805922998149)
      ·
        refine ⟨1017982877874151110562153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5429242015328805922998149 1017982877874151110562153)
        ·
          refine ⟨763487158405613332921615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1017982877874151110562153 763487158405613332921615)
          ·
            refine ⟨1145230737608419999382423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 763487158405613332921615 1145230737608419999382423)
            ·
              refine ⟨1717846106412629999073635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1145230737608419999382423 1717846106412629999073635)
              ·
                refine ⟨2576769159618944998610453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1717846106412629999073635 2576769159618944998610453)
                ·
                  refine ⟨120786054357138046809865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2576769159618944998610453 120786054357138046809865)
                  ·
                    rfl

theorem cell22_1058535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 6].length) (baseStart_1058535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1058535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1058535 prefixEnd_1058535 := by exact prefixLift 1058535
  have htrace : WordTrace (prefixWord ++ tailWord_1058535) baseStart_1058535 baseEnd_1058535 := by
    simpa [prefixWord, tailWord_1058535, baseEnd_1058535] using wordTrace_append hprefix tailTrace_1058535
  have hstable : (prefixWord ++ tailWord_1058535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058535).length < 2 ^ (prefixWord ++ tailWord_1058535).sum := by decide
  have hdescent : baseEnd_1058535 < baseStart_1058535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058550 : List Nat := [5, 1, 1, 1, 1, 3, 4, 1, 2, 3]
def baseStart_1058550 : Nat := 118140960795 + 1058550 * 2 ^ 59
def prefixEnd_1058550 : Nat := 4983230072969 + 3 ^ 40 * 1058550 * 2
def baseEnd_1058550 : Nat := 362363297877959101304549

theorem tailTrace_1058550 : CollatzResearch.WordTrace tailWord_1058550 prefixEnd_1058550 362363297877959101304549 := by
  unfold tailWord_1058550
  simp only [CollatzResearch.WordTrace]
  refine ⟨2413030644691350674500319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25738993543374407194670069 2413030644691350674500319)
  ·
    refine ⟨3619545967037026011750479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2413030644691350674500319 3619545967037026011750479)
    ·
      refine ⟨5429318950555539017625719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3619545967037026011750479 5429318950555539017625719)
      ·
        refine ⟨8143978425833308526438579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5429318950555539017625719 8143978425833308526438579)
        ·
          refine ⟨12215967638749962789657869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8143978425833308526438579 12215967638749962789657869)
          ·
            refine ⟨4580987864531236046121701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12215967638749962789657869 4580987864531236046121701)
            ·
              refine ⟨858935224599606758647819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4580987864531236046121701 858935224599606758647819)
              ·
                refine ⟨1288402836899410137971729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 858935224599606758647819 1288402836899410137971729)
                ·
                  refine ⟨966302127674557603478797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1288402836899410137971729 966302127674557603478797)
                  ·
                    refine ⟨362363297877959101304549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 966302127674557603478797 362363297877959101304549)
                    ·
                      rfl

theorem cell22_1058550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_1058550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1058550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1058550 prefixEnd_1058550 := by exact prefixLift 1058550
  have htrace : WordTrace (prefixWord ++ tailWord_1058550) baseStart_1058550 baseEnd_1058550 := by
    simpa [prefixWord, tailWord_1058550, baseEnd_1058550] using wordTrace_append hprefix tailTrace_1058550
  have hstable : (prefixWord ++ tailWord_1058550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058550).length < 2 ^ (prefixWord ++ tailWord_1058550).sum := by decide
  have hdescent : baseEnd_1058550 < baseStart_1058550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058561 : List Nat := [1, 2, 4, 1, 1, 1, 2, 4, 3, 3]
def baseStart_1058561 : Nat := 118140960795 + 1058561 * 2 ^ 59
def prefixEnd_1058561 : Nat := 4983230072969 + 3 ^ 40 * 1058561 * 2
def baseEnd_1058561 : Nat := 362367063402758739279515

theorem tailTrace_1058561 : CollatzResearch.WordTrace tailWord_1058561 prefixEnd_1058561 362367063402758739279515 := by
  unfold tailWord_1058561
  simp only [CollatzResearch.WordTrace]
  refine ⟨38608891518021759670655537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25739261012014506447103691 38608891518021759670655537)
  ·
    refine ⟨28956668638516319752991653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38608891518021759670655537 28956668638516319752991653)
    ·
      refine ⟨5429375369721809953685935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28956668638516319752991653 5429375369721809953685935)
      ·
        refine ⟨8144063054582714930528903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5429375369721809953685935 8144063054582714930528903)
        ·
          refine ⟨12216094581874072395793355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8144063054582714930528903 12216094581874072395793355)
          ·
            refine ⟨18324141872811108593690033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12216094581874072395793355 18324141872811108593690033)
            ·
              refine ⟨13743106404608331445267525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18324141872811108593690033 13743106404608331445267525)
              ·
                refine ⟨2576832450864062145987661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13743106404608331445267525 2576832450864062145987661)
                ·
                  refine ⟨966312169074023304745373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2576832450864062145987661 966312169074023304745373)
                  ·
                    refine ⟨362367063402758739279515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 966312169074023304745373 362367063402758739279515)
                    ·
                      rfl

theorem cell22_1058561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_1058561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1058561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1058561 prefixEnd_1058561 := by exact prefixLift 1058561
  have htrace : WordTrace (prefixWord ++ tailWord_1058561) baseStart_1058561 baseEnd_1058561 := by
    simpa [prefixWord, tailWord_1058561, baseEnd_1058561] using wordTrace_append hprefix tailTrace_1058561
  have hstable : (prefixWord ++ tailWord_1058561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058561).length < 2 ^ (prefixWord ++ tailWord_1058561).sum := by decide
  have hdescent : baseEnd_1058561 < baseStart_1058561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058574 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 9]
def baseStart_1058574 : Nat := 118140960795 + 1058574 * 2 ^ 59
def prefixEnd_1058574 : Nat := 4983230072969 + 3 ^ 40 * 1058574 * 2
def baseEnd_1058574 : Nat := 120790504522810346234825

theorem tailTrace_1058574 : CollatzResearch.WordTrace tailWord_1058574 prefixEnd_1058574 120790504522810346234825 := by
  unfold tailWord_1058574
  simp only [CollatzResearch.WordTrace]
  refine ⟨4826170708371832861359847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25739577111316441927252517 4826170708371832861359847)
  ·
    refine ⟨7239256062557749292039771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4826170708371832861359847 7239256062557749292039771)
    ·
      refine ⟨10858884093836623938059657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7239256062557749292039771 10858884093836623938059657)
      ·
        refine ⟨8144163070377467953544743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10858884093836623938059657 8144163070377467953544743)
        ·
          refine ⟨12216244605566201930317115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8144163070377467953544743 12216244605566201930317115)
          ·
            refine ⟨18324366908349302895475673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12216244605566201930317115 18324366908349302895475673)
            ·
              refine ⟨13743275181261977171606755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18324366908349302895475673 13743275181261977171606755)
              ·
                refine ⟨20614912771892965757410133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13743275181261977171606755 20614912771892965757410133)
                ·
                  refine ⟨120790504522810346234825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 20614912771892965757410133 120790504522810346234825)
                  ·
                    rfl

theorem cell22_1058574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_1058574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1058574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1058574 prefixEnd_1058574 := by exact prefixLift 1058574
  have htrace : WordTrace (prefixWord ++ tailWord_1058574) baseStart_1058574 baseEnd_1058574 := by
    simpa [prefixWord, tailWord_1058574, baseEnd_1058574] using wordTrace_append hprefix tailTrace_1058574
  have hstable : (prefixWord ++ tailWord_1058574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058574).length < 2 ^ (prefixWord ++ tailWord_1058574).sum := by decide
  have hdescent : baseEnd_1058574 < baseStart_1058574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058580 : List Nat := [2, 4, 4, 1, 2, 9]
def baseStart_1058580 : Nat := 118140960795 + 1058580 * 2 ^ 59
def prefixEnd_1058580 : Nat := 4983230072969 + 3 ^ 40 * 1058580 * 2
def baseEnd_1058580 : Nat := 4473747746803074358697

theorem tailTrace_1058580 : CollatzResearch.WordTrace tailWord_1058580 prefixEnd_1058580 4473747746803074358697 := by
  unfold tailWord_1058580
  simp only [CollatzResearch.WordTrace]
  refine ⟨19304792252476462957798597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25739723003301950610398129 19304792252476462957798597)
  ·
    refine ⟨3619648547339336804587237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19304792252476462957798597 3619648547339336804587237)
    ·
      refine ⟨678684102626125650860107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3619648547339336804587237 678684102626125650860107)
      ·
        refine ⟨1018026153939188476290161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 678684102626125650860107 1018026153939188476290161)
        ·
          refine ⟨763519615454391357217621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1018026153939188476290161 763519615454391357217621)
          ·
            refine ⟨4473747746803074358697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 763519615454391357217621 4473747746803074358697)
            ·
              rfl

theorem cell22_1058580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 9].length) (baseStart_1058580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1058580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1058580 prefixEnd_1058580 := by exact prefixLift 1058580
  have htrace : WordTrace (prefixWord ++ tailWord_1058580) baseStart_1058580 baseEnd_1058580 := by
    simpa [prefixWord, tailWord_1058580, baseEnd_1058580] using wordTrace_append hprefix tailTrace_1058580
  have hstable : (prefixWord ++ tailWord_1058580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058580).length < 2 ^ (prefixWord ++ tailWord_1058580).sum := by decide
  have hdescent : baseEnd_1058580 < baseStart_1058580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058591 : List Nat := [1, 1, 2, 4, 2, 1, 4, 2, 5]
def baseStart_1058591 : Nat := 118140960795 + 1058591 * 2 ^ 59
def prefixEnd_1058591 : Nat := 4983230072969 + 3 ^ 40 * 1058591 * 2
def baseEnd_1058591 : Nat := 120792444338616220343141

theorem tailTrace_1058591 : CollatzResearch.WordTrace tailWord_1058591 prefixEnd_1058591 120792444338616220343141 := by
  unfold tailWord_1058591
  simp only [CollatzResearch.WordTrace]
  refine ⟨38609985707913074794247627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25739990471942049862831751 38609985707913074794247627)
  ·
    refine ⟨57914978561869612191371441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38609985707913074794247627 57914978561869612191371441)
    ·
      refine ⟨43436233921402209143528581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57914978561869612191371441 43436233921402209143528581)
      ·
        refine ⟨8144293860262914214411609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43436233921402209143528581 8144293860262914214411609)
        ·
          refine ⟨6108220395197185660808707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8144293860262914214411609 6108220395197185660808707)
          ·
            refine ⟨9162330592795778491213061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6108220395197185660808707 9162330592795778491213061)
            ·
              refine ⟨1717936986149208467102449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9162330592795778491213061 1717936986149208467102449)
              ·
                refine ⟨1288452739611906350326837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1717936986149208467102449 1288452739611906350326837)
                ·
                  refine ⟨120792444338616220343141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1288452739611906350326837 120792444338616220343141)
                  ·
                    rfl

theorem cell22_1058591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 2, 5].length) (baseStart_1058591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1058591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1058591 prefixEnd_1058591 := by exact prefixLift 1058591
  have htrace : WordTrace (prefixWord ++ tailWord_1058591) baseStart_1058591 baseEnd_1058591 := by
    simpa [prefixWord, tailWord_1058591, baseEnd_1058591] using wordTrace_append hprefix tailTrace_1058591
  have hstable : (prefixWord ++ tailWord_1058591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058591).length < 2 ^ (prefixWord ++ tailWord_1058591).sum := by decide
  have hdescent : baseEnd_1058591 < baseStart_1058591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058595 : List Nat := [1, 1, 1, 4, 2, 1, 6, 2, 1, 3]
def baseStart_1058595 : Nat := 118140960795 + 1058595 * 2 ^ 59
def prefixEnd_1058595 : Nat := 4983230072969 + 3 ^ 40 * 1058595 * 2
def baseEnd_1058595 : Nat := 362378702297593983929411

theorem tailTrace_1058595 : CollatzResearch.WordTrace tailWord_1058595 prefixEnd_1058595 362378702297593983929411 := by
  unfold tailWord_1058595
  simp only [CollatzResearch.WordTrace]
  refine ⟨38610131599898583477393239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25740087733265722318262159 38610131599898583477393239)
  ·
    refine ⟨57915197399847875216089859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38610131599898583477393239 57915197399847875216089859)
    ·
      refine ⟨86872796099771812824134789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57915197399847875216089859 86872796099771812824134789)
      ·
        refine ⟨16288649268707214904525273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86872796099771812824134789 16288649268707214904525273)
        ·
          refine ⟨12216486951530411178393955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16288649268707214904525273 12216486951530411178393955)
          ·
            refine ⟨18324730427295616767590933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12216486951530411178393955 18324730427295616767590933)
            ·
              refine ⟨858971738779482035980825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18324730427295616767590933 858971738779482035980825)
              ·
                refine ⟨644228804084611526985619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 858971738779482035980825 644228804084611526985619)
                ·
                  refine ⟨966343206126917290478429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 644228804084611526985619 966343206126917290478429)
                  ·
                    refine ⟨362378702297593983929411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 966343206126917290478429 362378702297593983929411)
                    ·
                      rfl

theorem cell22_1058595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 2, 1, 3].length) (baseStart_1058595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1058595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1058595 prefixEnd_1058595 := by exact prefixLift 1058595
  have htrace : WordTrace (prefixWord ++ tailWord_1058595) baseStart_1058595 baseEnd_1058595 := by
    simpa [prefixWord, tailWord_1058595, baseEnd_1058595] using wordTrace_append hprefix tailTrace_1058595
  have hstable : (prefixWord ++ tailWord_1058595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058595).length < 2 ^ (prefixWord ++ tailWord_1058595).sum := by decide
  have hdescent : baseEnd_1058595 < baseStart_1058595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058668 : List Nat := [2, 2, 1, 1, 4, 4, 1, 1, 1, 5]
def baseStart_1058668 : Nat := 118140960795 + 1058668 * 2 ^ 59
def prefixEnd_1058668 : Nat := 4983230072969 + 3 ^ 40 * 1058668 * 2
def baseEnd_1058668 : Nat := 362403691689446126854187

theorem tailTrace_1058668 : CollatzResearch.WordTrace tailWord_1058668 prefixEnd_1058668 362403691689446126854187 := by
  unfold tailWord_1058668
  simp only [CollatzResearch.WordTrace]
  refine ⟨19306397064317058472400329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25741862752422744629867105 19306397064317058472400329)
  ·
    refine ⟨14479797798237793854300247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19306397064317058472400329 14479797798237793854300247)
    ·
      refine ⟨21719696697356690781450371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14479797798237793854300247 21719696697356690781450371)
      ·
        refine ⟨32579545046035036172175557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21719696697356690781450371 32579545046035036172175557)
        ·
          refine ⟨6108664696131569282282917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32579545046035036172175557 6108664696131569282282917)
          ·
            refine ⟨1145374630524669240428047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6108664696131569282282917 1145374630524669240428047)
            ·
              refine ⟨1718061945787003860642071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1145374630524669240428047 1718061945787003860642071)
              ·
                refine ⟨2577092918680505790963107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1718061945787003860642071 2577092918680505790963107)
                ·
                  refine ⟨3865639378020758686444661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2577092918680505790963107 3865639378020758686444661)
                  ·
                    refine ⟨362403691689446126854187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3865639378020758686444661 362403691689446126854187)
                    ·
                      rfl

theorem cell22_1058668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 5].length) (baseStart_1058668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1058668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1058668 prefixEnd_1058668 := by exact prefixLift 1058668
  have htrace : WordTrace (prefixWord ++ tailWord_1058668) baseStart_1058668 baseEnd_1058668 := by
    simpa [prefixWord, tailWord_1058668, baseEnd_1058668] using wordTrace_append hprefix tailTrace_1058668
  have hstable : (prefixWord ++ tailWord_1058668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058668).length < 2 ^ (prefixWord ++ tailWord_1058668).sum := by decide
  have hdescent : baseEnd_1058668 < baseStart_1058668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058698 : List Nat := [3, 1, 2, 4, 2, 2, 8]
def baseStart_1058698 : Nat := 118140960795 + 1058698 * 2 ^ 59
def prefixEnd_1058698 : Nat := 4983230072969 + 3 ^ 40 * 1058698 * 2
def baseEnd_1058698 : Nat := 13422739307501335133485

theorem tailTrace_1058698 : CollatzResearch.WordTrace tailWord_1058698 prefixEnd_1058698 13422739307501335133485 := by
  unfold tailWord_1058698
  simp only [CollatzResearch.WordTrace]
  refine ⟨9653472079631358017098187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25742592212350288045595165 9653472079631358017098187)
  ·
    refine ⟨14480208119447037025647281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9653472079631358017098187 14480208119447037025647281)
    ·
      refine ⟨10860156089585277769235461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14480208119447037025647281 10860156089585277769235461)
      ·
        refine ⟨2036279266797239581731649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10860156089585277769235461 2036279266797239581731649)
        ·
          refine ⟨1527209450097929686298737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2036279266797239581731649 1527209450097929686298737)
          ·
            refine ⟨1145407087573447264724053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1527209450097929686298737 1145407087573447264724053)
            ·
              refine ⟨13422739307501335133485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1145407087573447264724053 13422739307501335133485)
              ·
                rfl

theorem cell22_1058698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 8].length) (baseStart_1058698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1058698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1058698 prefixEnd_1058698 := by exact prefixLift 1058698
  have htrace : WordTrace (prefixWord ++ tailWord_1058698) baseStart_1058698 baseEnd_1058698 := by
    simpa [prefixWord, tailWord_1058698, baseEnd_1058698] using wordTrace_append hprefix tailTrace_1058698
  have hstable : (prefixWord ++ tailWord_1058698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058698).length < 2 ^ (prefixWord ++ tailWord_1058698).sum := by decide
  have hdescent : baseEnd_1058698 < baseStart_1058698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058713 : List Nat := [1, 2, 1, 2, 1, 3, 5, 1, 3, 3]
def baseStart_1058713 : Nat := 118140960795 + 1058713 * 2 ^ 59
def prefixEnd_1058713 : Nat := 4983230072969 + 3 ^ 40 * 1058713 * 2
def baseEnd_1058713 : Nat := 362419096109081009479049

theorem tailTrace_1058713 : CollatzResearch.WordTrace tailWord_1058713 prefixEnd_1058713 362419096109081009479049 := by
  unfold tailWord_1058713
  simp only [CollatzResearch.WordTrace]
  refine ⟨38614435413471089630188793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25742956942314059753459195 38614435413471089630188793)
  ·
    refine ⟨28960826560103317222641595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38614435413471089630188793 28960826560103317222641595)
    ·
      refine ⟨43441239840154975833962393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28960826560103317222641595 43441239840154975833962393)
      ·
        refine ⟨32580929880116231875471795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43441239840154975833962393 32580929880116231875471795)
        ·
          refine ⟨48871394820174347813207693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32580929880116231875471795 48871394820174347813207693)
          ·
            refine ⟨18326773057565380429952885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48871394820174347813207693 18326773057565380429952885)
            ·
              refine ⟨1718134974146754415308083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18326773057565380429952885 1718134974146754415308083)
              ·
                refine ⟨2577202461220131622962125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1718134974146754415308083 2577202461220131622962125)
                ·
                  refine ⟨966450922957549358610797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2577202461220131622962125 966450922957549358610797)
                  ·
                    refine ⟨362419096109081009479049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 966450922957549358610797 362419096109081009479049)
                    ·
                      rfl

theorem cell22_1058713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 3, 3].length) (baseStart_1058713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1058713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1058713 prefixEnd_1058713 := by exact prefixLift 1058713
  have htrace : WordTrace (prefixWord ++ tailWord_1058713) baseStart_1058713 baseEnd_1058713 := by
    simpa [prefixWord, tailWord_1058713, baseEnd_1058713] using wordTrace_append hprefix tailTrace_1058713
  have hstable : (prefixWord ++ tailWord_1058713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058713).length < 2 ^ (prefixWord ++ tailWord_1058713).sum := by decide
  have hdescent : baseEnd_1058713 < baseStart_1058713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058719 : List Nat := [1, 1, 2, 5, 4, 1, 2, 1, 2, 3]
def baseStart_1058719 : Nat := 118140960795 + 1058719 * 2 ^ 59
def prefixEnd_1058719 : Nat := 4983230072969 + 3 ^ 40 * 1058719 * 2
def baseEnd_1058719 : Nat := 362421150031698993829031

theorem tailTrace_1058719 : CollatzResearch.WordTrace tailWord_1058719 prefixEnd_1058719 362421150031698993829031 := by
  unfold tailWord_1058719
  simp only [CollatzResearch.WordTrace]
  refine ⟨38614654251449352654907211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25743102834299568436604807 38614654251449352654907211)
  ·
    refine ⟨57921981377174028982360817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38614654251449352654907211 57921981377174028982360817)
    ·
      refine ⟨43441486032880521736770613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57921981377174028982360817 43441486032880521736770613)
      ·
        refine ⟨4072639315582548912822245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43441486032880521736770613 4072639315582548912822245)
        ·
          refine ⟨763619871671727921154171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4072639315582548912822245 763619871671727921154171)
          ·
            refine ⟨1145429807507591881731257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 763619871671727921154171 1145429807507591881731257)
            ·
              refine ⟨859072355630693911298443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1145429807507591881731257 859072355630693911298443)
              ·
                refine ⟨1288608533446040866947665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 859072355630693911298443 1288608533446040866947665)
                ·
                  refine ⟨966456400084530650210749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1288608533446040866947665 966456400084530650210749)
                  ·
                    refine ⟨362421150031698993829031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 966456400084530650210749 362421150031698993829031)
                    ·
                      rfl

theorem cell22_1058719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 1, 2, 3].length) (baseStart_1058719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1058719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1058719 prefixEnd_1058719 := by exact prefixLift 1058719
  have htrace : WordTrace (prefixWord ++ tailWord_1058719) baseStart_1058719 baseEnd_1058719 := by
    simpa [prefixWord, tailWord_1058719, baseEnd_1058719] using wordTrace_append hprefix tailTrace_1058719
  have hstable : (prefixWord ++ tailWord_1058719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058719).length < 2 ^ (prefixWord ++ tailWord_1058719).sum := by decide
  have hdescent : baseEnd_1058719 < baseStart_1058719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058734 : List Nat := [4, 1, 5, 1, 1, 1, 2, 1, 2, 4]
def baseStart_1058734 : Nat := 118140960795 + 1058734 * 2 ^ 59
def prefixEnd_1058734 : Nat := 4983230072969 + 3 ^ 40 * 1058734 * 2
def baseEnd_1058734 : Nat := 362426284838243954703985

theorem tailTrace_1058734 : CollatzResearch.WordTrace tailWord_1058734 prefixEnd_1058734 362426284838243954703985 := by
  unfold tailWord_1058734
  simp only [CollatzResearch.WordTrace]
  refine ⟨4826900168299376277087907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25743467564263340144468837 4826900168299376277087907)
  ·
    refine ⟨7240350252449064415631861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4826900168299376277087907 7240350252449064415631861)
    ·
      refine ⟨678782836167099788965487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7240350252449064415631861 678782836167099788965487)
      ·
        refine ⟨1018174254250649683448231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 678782836167099788965487 1018174254250649683448231)
        ·
          refine ⟨1527261381375974525172347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1018174254250649683448231 1527261381375974525172347)
          ·
            refine ⟨2290892072063961787758521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1527261381375974525172347 2290892072063961787758521)
            ·
              refine ⟨1718169054047971340818891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2290892072063961787758521 1718169054047971340818891)
              ·
                refine ⟨2577253581071957011228337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1718169054047971340818891 2577253581071957011228337)
                ·
                  refine ⟨1932940185803967758421253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2577253581071957011228337 1932940185803967758421253)
                  ·
                    refine ⟨362426284838243954703985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1932940185803967758421253 362426284838243954703985)
                    ·
                      rfl

theorem cell22_1058734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_1058734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1058734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1058734 prefixEnd_1058734 := by exact prefixLift 1058734
  have htrace : WordTrace (prefixWord ++ tailWord_1058734) baseStart_1058734 baseEnd_1058734 := by
    simpa [prefixWord, tailWord_1058734, baseEnd_1058734] using wordTrace_append hprefix tailTrace_1058734
  have hstable : (prefixWord ++ tailWord_1058734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058734).length < 2 ^ (prefixWord ++ tailWord_1058734).sum := by decide
  have hdescent : baseEnd_1058734 < baseStart_1058734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058764 : List Nat := [2, 2, 1, 4, 1, 4, 2, 2, 1, 3]
def baseStart_1058764 : Nat := 118140960795 + 1058764 * 2 ^ 59
def prefixEnd_1058764 : Nat := 4983230072969 + 3 ^ 40 * 1058764 * 2
def baseEnd_1058764 : Nat := 362436554451333876453893

theorem tailTrace_1058764 : CollatzResearch.WordTrace tailWord_1058764 prefixEnd_1058764 362436554451333876453893 := by
  unfold tailWord_1058764
  simp only [CollatzResearch.WordTrace]
  refine ⟨19308147768143162670147673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25744197024190883560196897 19308147768143162670147673)
  ·
    refine ⟨14481110826107372002610755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19308147768143162670147673 14481110826107372002610755)
    ·
      refine ⟨21721666239161058003916133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14481110826107372002610755 21721666239161058003916133)
      ·
        refine ⟨4072812419842698375734275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21721666239161058003916133 4072812419842698375734275)
        ·
          refine ⟨6109218629764047563601413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4072812419842698375734275 6109218629764047563601413)
          ·
            refine ⟨1145478493080758918175265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6109218629764047563601413 1145478493080758918175265)
            ·
              refine ⟨859108869810569188631449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1145478493080758918175265 859108869810569188631449)
              ·
                refine ⟨644331652357926891473587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 859108869810569188631449 644331652357926891473587)
                ·
                  refine ⟨966497478536890337210381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 644331652357926891473587 966497478536890337210381)
                  ·
                    refine ⟨362436554451333876453893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 966497478536890337210381 362436554451333876453893)
                    ·
                      rfl

theorem cell22_1058764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 2, 1, 3].length) (baseStart_1058764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1058764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1058764 prefixEnd_1058764 := by exact prefixLift 1058764
  have htrace : WordTrace (prefixWord ++ tailWord_1058764) baseStart_1058764 baseEnd_1058764 := by
    simpa [prefixWord, tailWord_1058764, baseEnd_1058764] using wordTrace_append hprefix tailTrace_1058764
  have hstable : (prefixWord ++ tailWord_1058764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058764).length < 2 ^ (prefixWord ++ tailWord_1058764).sum := by decide
  have hdescent : baseEnd_1058764 < baseStart_1058764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058773 : List Nat := [1, 3, 2, 3, 2, 1, 1, 2, 3, 4]
def baseStart_1058773 : Nat := 118140960795 + 1058773 * 2 ^ 59
def prefixEnd_1058773 : Nat := 4983230072969 + 3 ^ 40 * 1058773 * 2
def baseEnd_1058773 : Nat := 362439635335260852978865

theorem tailTrace_1058773 : CollatzResearch.WordTrace tailWord_1058773 prefixEnd_1058773 362439635335260852978865 := by
  unfold tailWord_1058773
  simp only [CollatzResearch.WordTrace]
  refine ⟨38616623793253719877372973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25744415862169146584915315 38616623793253719877372973)
  ·
    refine ⟨14481233922470144954014865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38616623793253719877372973 14481233922470144954014865)
    ·
      refine ⟨10860925441852608715511149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14481233922470144954014865 10860925441852608715511149)
      ·
        refine ⟨4072847040694728268316681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10860925441852608715511149 4072847040694728268316681)
        ·
          refine ⟨3054635280521046201237511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4072847040694728268316681 3054635280521046201237511)
          ·
            refine ⟨4581952920781569301856267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3054635280521046201237511 4581952920781569301856267)
            ·
              refine ⟨6872929381172353952784401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4581952920781569301856267 6872929381172353952784401)
              ·
                refine ⟨5154697035879265464588301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6872929381172353952784401 5154697035879265464588301)
                ·
                  refine ⟨1933011388454724549220613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5154697035879265464588301 1933011388454724549220613)
                  ·
                    refine ⟨362439635335260852978865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1933011388454724549220613 362439635335260852978865)
                    ·
                      rfl

theorem cell22_1058773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_1058773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1058773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1058773 prefixEnd_1058773 := by exact prefixLift 1058773
  have htrace : WordTrace (prefixWord ++ tailWord_1058773) baseStart_1058773 baseEnd_1058773 := by
    simpa [prefixWord, tailWord_1058773, baseEnd_1058773] using wordTrace_append hprefix tailTrace_1058773
  have hstable : (prefixWord ++ tailWord_1058773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058773).length < 2 ^ (prefixWord ++ tailWord_1058773).sum := by decide
  have hdescent : baseEnd_1058773 < baseStart_1058773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058837 : List Nat := [1, 3, 2, 1, 6, 1, 1, 1, 1, 5]
def baseStart_1058837 : Nat := 118140960795 + 1058837 * 2 ^ 59
def prefixEnd_1058837 : Nat := 4983230072969 + 3 ^ 40 * 1058837 * 2
def baseEnd_1058837 : Nat := 362461543843186019378669

theorem tailTrace_1058837 : CollatzResearch.WordTrace tailWord_1058837 prefixEnd_1058837 362461543843186019378669 := by
  unfold tailWord_1058837
  simp only [CollatzResearch.WordTrace]
  refine ⟨38618958065021858807702765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25745972043347905871801843 38618958065021858807702765)
  ·
    refine ⟨14482109274383197052888537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38618958065021858807702765 14482109274383197052888537)
    ·
      refine ⟨10861581955787397789666403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14482109274383197052888537 10861581955787397789666403)
      ·
        refine ⟨16292372933681096684499605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10861581955787397789666403 16292372933681096684499605)
        ·
          refine ⟨763704981266301407085919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16292372933681096684499605 763704981266301407085919)
          ·
            refine ⟨1145557471899452110628879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 763704981266301407085919 1145557471899452110628879)
            ·
              refine ⟨1718336207849178165943319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1145557471899452110628879 1718336207849178165943319)
              ·
                refine ⟨2577504311773767248914979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1718336207849178165943319 2577504311773767248914979)
                ·
                  refine ⟨3866256467660650873372469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2577504311773767248914979 3866256467660650873372469)
                  ·
                    refine ⟨362461543843186019378669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3866256467660650873372469 362461543843186019378669)
                    ·
                      rfl

theorem cell22_1058837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 1, 5].length) (baseStart_1058837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1058837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1058837 prefixEnd_1058837 := by exact prefixLift 1058837
  have htrace : WordTrace (prefixWord ++ tailWord_1058837) baseStart_1058837 baseEnd_1058837 := by
    simpa [prefixWord, tailWord_1058837, baseEnd_1058837] using wordTrace_append hprefix tailTrace_1058837
  have hstable : (prefixWord ++ tailWord_1058837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058837).length < 2 ^ (prefixWord ++ tailWord_1058837).sum := by decide
  have hdescent : baseEnd_1058837 < baseStart_1058837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058856 : List Nat := [2, 1, 5, 3, 2, 1, 1, 3, 4]
def baseStart_1058856 : Nat := 118140960795 + 1058856 * 2 ^ 59
def prefixEnd_1058856 : Nat := 4983230072969 + 3 ^ 40 * 1058856 * 2
def baseEnd_1058856 : Nat := 120822682643825434384537

theorem tailTrace_1058856 : CollatzResearch.WordTrace tailWord_1058856 prefixEnd_1058856 120822682643825434384537 := by
  unfold tailWord_1058856
  simp only [CollatzResearch.WordTrace]
  refine ⟨19309825525976512526322211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25746434034635350035096281 19309825525976512526322211)
  ·
    refine ⟨28964738288964768789483317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19309825525976512526322211 28964738288964768789483317)
    ·
      refine ⟨2715444214590447074014061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28964738288964768789483317 2715444214590447074014061)
      ·
        refine ⟨1018291580471417652755273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2715444214590447074014061 1018291580471417652755273)
        ·
          refine ⟨763718685353563239566455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1018291580471417652755273 763718685353563239566455)
          ·
            refine ⟨1145578028030344859349683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 763718685353563239566455 1145578028030344859349683)
            ·
              refine ⟨1718367042045517289024525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1145578028030344859349683 1718367042045517289024525)
              ·
                refine ⟨644387640767068983384197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1718367042045517289024525 644387640767068983384197)
                ·
                  refine ⟨120822682643825434384537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 644387640767068983384197 120822682643825434384537)
                  ·
                    rfl

theorem cell22_1058856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 3, 4].length) (baseStart_1058856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1058856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1058856 prefixEnd_1058856 := by exact prefixLift 1058856
  have htrace : WordTrace (prefixWord ++ tailWord_1058856) baseStart_1058856 baseEnd_1058856 := by
    simpa [prefixWord, tailWord_1058856, baseEnd_1058856] using wordTrace_append hprefix tailTrace_1058856
  have hstable : (prefixWord ++ tailWord_1058856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058856).length < 2 ^ (prefixWord ++ tailWord_1058856).sum := by decide
  have hdescent : baseEnd_1058856 < baseStart_1058856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058953 : List Nat := [1, 2, 1, 1, 4, 2, 2, 2, 1, 6]
def baseStart_1058953 : Nat := 118140960795 + 1058953 * 2 ^ 59
def prefixEnd_1058953 : Nat := 4983230072969 + 3 ^ 40 * 1058953 * 2
def baseEnd_1058953 : Nat := 362501253013800383478313

theorem tailTrace_1058953 : CollatzResearch.WordTrace tailWord_1058953 prefixEnd_1058953 362501253013800383478313 := by
  unfold tailWord_1058953
  simp only [CollatzResearch.WordTrace]
  refine ⟨38623188932601610618925513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25748792621734407079283675 38623188932601610618925513)
  ·
    refine ⟨28967391699451207964194135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38623188932601610618925513 28967391699451207964194135)
    ·
      refine ⟨43451087549176811946291203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28967391699451207964194135 43451087549176811946291203)
      ·
        refine ⟨65176631323765217919436805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43451087549176811946291203 65176631323765217919436805)
        ·
          refine ⟨12220618373205978359894401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65176631323765217919436805 12220618373205978359894401)
          ·
            refine ⟨9165463779904483769920801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12220618373205978359894401 9165463779904483769920801)
            ·
              refine ⟨6874097834928362827440601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9165463779904483769920801 6874097834928362827440601)
              ·
                refine ⟨5155573376196272120580451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6874097834928362827440601 5155573376196272120580451)
                ·
                  refine ⟨7733360064294408180870677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5155573376196272120580451 7733360064294408180870677)
                  ·
                    refine ⟨362501253013800383478313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7733360064294408180870677 362501253013800383478313)
                    ·
                      rfl

theorem cell22_1058953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 6].length) (baseStart_1058953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1058953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1058953 prefixEnd_1058953 := by exact prefixLift 1058953
  have htrace : WordTrace (prefixWord ++ tailWord_1058953) baseStart_1058953 baseEnd_1058953 := by
    simpa [prefixWord, tailWord_1058953, baseEnd_1058953] using wordTrace_append hprefix tailTrace_1058953
  have hstable : (prefixWord ++ tailWord_1058953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058953).length < 2 ^ (prefixWord ++ tailWord_1058953).sum := by decide
  have hdescent : baseEnd_1058953 < baseStart_1058953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058989 : List Nat := [1, 5, 2, 1, 2, 1, 3, 2, 2, 3]
def baseStart_1058989 : Nat := 118140960795 + 1058989 * 2 ^ 59
def prefixEnd_1058989 : Nat := 4983230072969 + 3 ^ 40 * 1058989 * 2
def baseEnd_1058989 : Nat := 362513576549508289578203

theorem tailTrace_1058989 : CollatzResearch.WordTrace tailWord_1058989 prefixEnd_1058989 362513576549508289578203 := by
  unfold tailWord_1058989
  simp only [CollatzResearch.WordTrace]
  refine ⟨38624501960471188767236021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25749667973647459178157347 38624501960471188767236021)
  ·
    refine ⟨3621047058794173946928377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38624501960471188767236021 3621047058794173946928377)
    ·
      refine ⟨2715785294095630460196283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3621047058794173946928377 2715785294095630460196283)
      ·
        refine ⟨4073677941143445690294425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2715785294095630460196283 4073677941143445690294425)
        ·
          refine ⟨3055258455857584267720819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4073677941143445690294425 3055258455857584267720819)
          ·
            refine ⟨4582887683786376401581229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3055258455857584267720819 4582887683786376401581229)
            ·
              refine ⟨1718582881419891150592961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4582887683786376401581229 1718582881419891150592961)
              ·
                refine ⟨1288937161064918362944721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1718582881419891150592961 1288937161064918362944721)
                ·
                  refine ⟨966702870798688772208541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1288937161064918362944721 966702870798688772208541)
                  ·
                    refine ⟨362513576549508289578203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 966702870798688772208541 362513576549508289578203)
                    ·
                      rfl

theorem cell22_1058989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_1058989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1058989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1058989 prefixEnd_1058989 := by exact prefixLift 1058989
  have htrace : WordTrace (prefixWord ++ tailWord_1058989) baseStart_1058989 baseEnd_1058989 := by
    simpa [prefixWord, tailWord_1058989, baseEnd_1058989] using wordTrace_append hprefix tailTrace_1058989
  have hstable : (prefixWord ++ tailWord_1058989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058989).length < 2 ^ (prefixWord ++ tailWord_1058989).sum := by decide
  have hdescent : baseEnd_1058989 < baseStart_1058989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059006 : List Nat := [4, 2, 1, 1, 4, 1, 3, 1, 2, 3]
def baseStart_1059006 : Nat := 118140960795 + 1059006 * 2 ^ 59
def prefixEnd_1059006 : Nat := 4983230072969 + 3 ^ 40 * 1059006 * 2
def baseEnd_1059006 : Nat := 362519395996925911903151

theorem tailTrace_1059006 : CollatzResearch.WordTrace tailWord_1059006 prefixEnd_1059006 362519395996925911903151 := by
  unfold tailWord_1059006
  simp only [CollatzResearch.WordTrace]
  refine ⟨4828140250176200083825609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25750081334273067113736581 4828140250176200083825609)
  ·
    refine ⟨3621105187632150062869207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4828140250176200083825609 3621105187632150062869207)
    ·
      refine ⟨5431657781448225094303811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3621105187632150062869207 5431657781448225094303811)
      ·
        refine ⟨8147486672172337641455717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5431657781448225094303811 8147486672172337641455717)
        ·
          refine ⟨1527653751032313307772947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8147486672172337641455717 1527653751032313307772947)
          ·
            refine ⟨2291480626548469961659421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1527653751032313307772947 2291480626548469961659421)
            ·
              refine ⟨859305234955676235622283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2291480626548469961659421 859305234955676235622283)
              ·
                refine ⟨1288957852433514353433425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 859305234955676235622283 1288957852433514353433425)
                ·
                  refine ⟨966718389325135765075069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1288957852433514353433425 966718389325135765075069)
                  ·
                    refine ⟨362519395996925911903151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 966718389325135765075069 362519395996925911903151)
                    ·
                      rfl

theorem cell22_1059006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_1059006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1059006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1059006 prefixEnd_1059006 := by exact prefixLift 1059006
  have htrace : WordTrace (prefixWord ++ tailWord_1059006) baseStart_1059006 baseEnd_1059006 := by
    simpa [prefixWord, tailWord_1059006, baseEnd_1059006] using wordTrace_append hprefix tailTrace_1059006
  have hstable : (prefixWord ++ tailWord_1059006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059006).length < 2 ^ (prefixWord ++ tailWord_1059006).sum := by decide
  have hdescent : baseEnd_1059006 < baseStart_1059006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059034 : List Nat := [3, 1, 1, 2, 2, 1, 5, 3, 1, 3]
def baseStart_1059034 : Nat := 118140960795 + 1059034 * 2 ^ 59
def prefixEnd_1059034 : Nat := 4983230072969 + 3 ^ 40 * 1059034 * 2
def baseEnd_1059034 : Nat := 362528980969143172203065

theorem tailTrace_1059034 : CollatzResearch.WordTrace tailWord_1059034 prefixEnd_1059034 362528980969143172203065 := by
  unfold tailWord_1059034
  simp only [CollatzResearch.WordTrace]
  refine ⟨9656535811327040363156039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25750762163538774301749437 9656535811327040363156039)
  ·
    refine ⟨14484803716990560544734059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9656535811327040363156039 14484803716990560544734059)
    ·
      refine ⟨21727205575485840817101089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14484803716990560544734059 21727205575485840817101089)
      ·
        refine ⟨16295404181614380612825817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21727205575485840817101089 16295404181614380612825817)
        ·
          refine ⟨12221553136210785459619363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16295404181614380612825817 12221553136210785459619363)
          ·
            refine ⟨18332329704316178189429045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12221553136210785459619363 18332329704316178189429045)
            ·
              refine ⟨1718655909779641705258973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18332329704316178189429045 1718655909779641705258973)
              ·
                refine ⟨644495966167365639472115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1718655909779641705258973 644495966167365639472115)
                ·
                  refine ⟨966743949251048459208173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 644495966167365639472115 966743949251048459208173)
                  ·
                    refine ⟨362528980969143172203065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 966743949251048459208173 362528980969143172203065)
                    ·
                      rfl

theorem cell22_1059034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 3, 1, 3].length) (baseStart_1059034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1059034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1059034 prefixEnd_1059034 := by exact prefixLift 1059034
  have htrace : WordTrace (prefixWord ++ tailWord_1059034) baseStart_1059034 baseEnd_1059034 := by
    simpa [prefixWord, tailWord_1059034, baseEnd_1059034] using wordTrace_append hprefix tailTrace_1059034
  have hstable : (prefixWord ++ tailWord_1059034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059034).length < 2 ^ (prefixWord ++ tailWord_1059034).sum := by decide
  have hdescent : baseEnd_1059034 < baseStart_1059034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059109 : List Nat := [1, 3, 1, 2, 5, 1, 1, 4, 4]
def baseStart_1059109 : Nat := 118140960795 + 1059109 * 2 ^ 59
def prefixEnd_1059109 : Nat := 4983230072969 + 3 ^ 40 * 1059109 * 2
def baseEnd_1059109 : Nat := 120851551667289325525945

theorem tailTrace_1059109 : CollatzResearch.WordTrace tailWord_1059109 prefixEnd_1059109 120851551667289325525945 := by
  unfold tailWord_1059109
  simp only [CollatzResearch.WordTrace]
  refine ⟨38628878720036449261604381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25752585813357632841069587 38628878720036449261604381)
  ·
    refine ⟨14485829520013668473101643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38628878720036449261604381 14485829520013668473101643)
    ·
      refine ⟨21728744280020502709652465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14485829520013668473101643 21728744280020502709652465)
      ·
        refine ⟨16296558210015377032239349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21728744280020502709652465 16296558210015377032239349)
        ·
          refine ⟨1527802332188941596772439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16296558210015377032239349 1527802332188941596772439)
          ·
            refine ⟨2291703498283412395158659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1527802332188941596772439 2291703498283412395158659)
            ·
              refine ⟨3437555247425118592737989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2291703498283412395158659 3437555247425118592737989)
              ·
                refine ⟨644541608892209736138373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3437555247425118592737989 644541608892209736138373)
                ·
                  refine ⟨120851551667289325525945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 644541608892209736138373 120851551667289325525945)
                  ·
                    rfl

theorem cell22_1059109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 4, 4].length) (baseStart_1059109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1059109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1059109 prefixEnd_1059109 := by exact prefixLift 1059109
  have htrace : WordTrace (prefixWord ++ tailWord_1059109) baseStart_1059109 baseEnd_1059109 := by
    simpa [prefixWord, tailWord_1059109, baseEnd_1059109] using wordTrace_append hprefix tailTrace_1059109
  have hstable : (prefixWord ++ tailWord_1059109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059109).length < 2 ^ (prefixWord ++ tailWord_1059109).sum := by decide
  have hdescent : baseEnd_1059109 < baseStart_1059109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059124 : List Nat := [2, 5, 1, 1, 1, 3, 2, 1, 1, 5]
def baseStart_1059124 : Nat := 118140960795 + 1059124 * 2 ^ 59
def prefixEnd_1059124 : Nat := 4983230072969 + 3 ^ 40 * 1059124 * 2
def baseEnd_1059124 : Nat := 362559789808412937452789

theorem tailTrace_1059124 : CollatzResearch.WordTrace tailWord_1059124 prefixEnd_1059124 362559789808412937452789 := by
  unfold tailWord_1059124
  simp only [CollatzResearch.WordTrace]
  refine ⟨19314712907491053411700213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25752950543321404548933617 19314712907491053411700213)
  ·
    refine ⟨1810754335077286257346895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19314712907491053411700213 1810754335077286257346895)
    ·
      refine ⟨2716131502615929386020343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1810754335077286257346895 2716131502615929386020343)
      ·
        refine ⟨4074197253923894079030515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2716131502615929386020343 4074197253923894079030515)
        ·
          refine ⟨6111295880885841118545773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4074197253923894079030515 6111295880885841118545773)
          ·
            refine ⟨2291735955332190419454665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6111295880885841118545773 2291735955332190419454665)
            ·
              refine ⟨1718801966499142814590999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2291735955332190419454665 1718801966499142814590999)
              ·
                refine ⟨2578202949748714221886499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1718801966499142814590999 2578202949748714221886499)
                ·
                  refine ⟨3867304424623071332829749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2578202949748714221886499 3867304424623071332829749)
                  ·
                    refine ⟨362559789808412937452789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3867304424623071332829749 362559789808412937452789)
                    ·
                      rfl

theorem cell22_1059124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_1059124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1059124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1059124 prefixEnd_1059124 := by exact prefixLift 1059124
  have htrace : WordTrace (prefixWord ++ tailWord_1059124) baseStart_1059124 baseEnd_1059124 := by
    simpa [prefixWord, tailWord_1059124, baseEnd_1059124] using wordTrace_append hprefix tailTrace_1059124
  have hstable : (prefixWord ++ tailWord_1059124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059124).length < 2 ^ (prefixWord ++ tailWord_1059124).sum := by decide
  have hdescent : baseEnd_1059124 < baseStart_1059124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059150 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 1, 8]
def baseStart_1059150 : Nat := 118140960795 + 1059150 * 2 ^ 59
def prefixEnd_1059150 : Nat := 4983230072969 + 3 ^ 40 * 1059150 * 2
def baseEnd_1059150 : Nat := 362568690139757536302709

theorem tailTrace_1059150 : CollatzResearch.WordTrace tailWord_1059150 prefixEnd_1059150 362568690139757536302709 := by
  unfold tailWord_1059150
  simp only [CollatzResearch.WordTrace]
  refine ⟨4828796764110989157980863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25753582741925275509231269 4828796764110989157980863)
  ·
    refine ⟨7243195146166483736971295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4828796764110989157980863 7243195146166483736971295)
    ·
      refine ⟨10864792719249725605456943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7243195146166483736971295 10864792719249725605456943)
      ·
        refine ⟨16297189078874588408185415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10864792719249725605456943 16297189078874588408185415)
        ·
          refine ⟨24445783618311882612278123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16297189078874588408185415 24445783618311882612278123)
          ·
            refine ⟨36668675427467823918417185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24445783618311882612278123 36668675427467823918417185)
            ·
              refine ⟨27501506570600867938812889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36668675427467823918417185 27501506570600867938812889)
              ·
                refine ⟨20626129927950650954109667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27501506570600867938812889 20626129927950650954109667)
                ·
                  refine ⟨30939194891925976431164501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20626129927950650954109667 30939194891925976431164501)
                  ·
                    refine ⟨362568690139757536302709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 30939194891925976431164501 362568690139757536302709)
                    ·
                      rfl

theorem cell22_1059150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_1059150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1059150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1059150 prefixEnd_1059150 := by exact prefixLift 1059150
  have htrace : WordTrace (prefixWord ++ tailWord_1059150) baseStart_1059150 baseEnd_1059150 := by
    simpa [prefixWord, tailWord_1059150, baseEnd_1059150] using wordTrace_append hprefix tailTrace_1059150
  have hstable : (prefixWord ++ tailWord_1059150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059150).length < 2 ^ (prefixWord ++ tailWord_1059150).sum := by decide
  have hdescent : baseEnd_1059150 < baseStart_1059150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059203 : List Nat := [1, 1, 1, 3, 6, 2, 1, 3, 1, 3]
def baseStart_1059203 : Nat := 118140960795 + 1059203 * 2 ^ 59
def prefixEnd_1059203 : Nat := 4983230072969 + 3 ^ 40 * 1059203 * 2
def baseEnd_1059203 : Nat := 362586833122883064727547

theorem tailTrace_1059203 : CollatzResearch.WordTrace tailWord_1059203 prefixEnd_1059203 362586833122883064727547 := by
  unfold tailWord_1059203
  simp only [CollatzResearch.WordTrace]
  refine ⟨38632307181695903315526263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25754871454463935543684175 38632307181695903315526263)
  ·
    refine ⟨57948460772543854973289395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38632307181695903315526263 57948460772543854973289395)
    ·
      refine ⟨86922691158815782459934093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57948460772543854973289395 86922691158815782459934093)
      ·
        refine ⟨32596009184555918422475285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86922691158815782459934093 32596009184555918422475285)
        ·
          refine ⟨1527937930526058676053529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 32596009184555918422475285 1527937930526058676053529)
          ·
            refine ⟨1145953447894544007040147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1527937930526058676053529 1145953447894544007040147)
            ·
              refine ⟨1718930171841816010560221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1145953447894544007040147 1718930171841816010560221)
              ·
                refine ⟨644598814440681003960083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1718930171841816010560221 644598814440681003960083)
                ·
                  refine ⟨966898221661021505940125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 644598814440681003960083 966898221661021505940125)
                  ·
                    refine ⟨362586833122883064727547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 966898221661021505940125 362586833122883064727547)
                    ·
                      rfl

theorem cell22_1059203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 3, 1, 3].length) (baseStart_1059203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1059203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1059203 prefixEnd_1059203 := by exact prefixLift 1059203
  have htrace : WordTrace (prefixWord ++ tailWord_1059203) baseStart_1059203 baseEnd_1059203 := by
    simpa [prefixWord, tailWord_1059203, baseEnd_1059203] using wordTrace_append hprefix tailTrace_1059203
  have hstable : (prefixWord ++ tailWord_1059203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059203).length < 2 ^ (prefixWord ++ tailWord_1059203).sum := by decide
  have hdescent : baseEnd_1059203 < baseStart_1059203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059220 : List Nat := [2, 4, 2, 1, 3, 1, 3, 2, 1, 3]
def baseStart_1059220 : Nat := 118140960795 + 1059220 * 2 ^ 59
def prefixEnd_1059220 : Nat := 4983230072969 + 3 ^ 40 * 1059220 * 2
def baseEnd_1059220 : Nat := 362592652570300687052495

theorem tailTrace_1059220 : CollatzResearch.WordTrace tailWord_1059220 prefixEnd_1059220 362592652570300687052495 := by
  unfold tailWord_1059220
  simp only [CollatzResearch.WordTrace]
  refine ⟨19316463611317157609447557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25755284815089543479263409 19316463611317157609447557)
  ·
    refine ⟨3621836927121967051771417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19316463611317157609447557 3621836927121967051771417)
    ·
      refine ⟨2716377695341475288828563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3621836927121967051771417 2716377695341475288828563)
      ·
        refine ⟨4074566543012212933242845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2716377695341475288828563 4074566543012212933242845)
        ·
          refine ⟨1527962453629579849966067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4074566543012212933242845 1527962453629579849966067)
          ·
            refine ⟨2291943680444369774949101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1527962453629579849966067 2291943680444369774949101)
            ·
              refine ⟨859478880166638665605913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2291943680444369774949101 859478880166638665605913)
              ·
                refine ⟨644609160124978999204435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 859478880166638665605913 644609160124978999204435)
                ·
                  refine ⟨966913740187468498806653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 644609160124978999204435 966913740187468498806653)
                  ·
                    refine ⟨362592652570300687052495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 966913740187468498806653 362592652570300687052495)
                    ·
                      rfl

theorem cell22_1059220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_1059220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1059220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1059220 prefixEnd_1059220 := by exact prefixLift 1059220
  have htrace : WordTrace (prefixWord ++ tailWord_1059220) baseStart_1059220 baseEnd_1059220 := by
    simpa [prefixWord, tailWord_1059220, baseEnd_1059220] using wordTrace_append hprefix tailTrace_1059220
  have hstable : (prefixWord ++ tailWord_1059220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059220).length < 2 ^ (prefixWord ++ tailWord_1059220).sum := by decide
  have hdescent : baseEnd_1059220 < baseStart_1059220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059233 : List Nat := [1, 2, 3, 5, 1, 2, 2, 1, 5]
def baseStart_1059233 : Nat := 118140960795 + 1059233 * 2 ^ 59
def prefixEnd_1059233 : Nat := 4983230072969 + 3 ^ 40 * 1059233 * 2
def baseEnd_1059233 : Nat := 120865700911990995492485

theorem tailTrace_1059233 : CollatzResearch.WordTrace tailWord_1059233 prefixEnd_1059233 120865700911990995492485 := by
  unfold tailWord_1059233
  simp only [CollatzResearch.WordTrace]
  refine ⟨38633401371587218439118353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25755600914391478959412235 38633401371587218439118353)
  ·
    refine ⟨28975051028690413829338765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38633401371587218439118353 28975051028690413829338765)
    ·
      refine ⟨10865644135758905186002037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28975051028690413829338765 10865644135758905186002037)
      ·
        refine ⟨1018654137727397361187691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10865644135758905186002037 1018654137727397361187691)
        ·
          refine ⟨1527981206591096041781537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1018654137727397361187691 1527981206591096041781537)
          ·
            refine ⟨1145985904943322031336153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1527981206591096041781537 1145985904943322031336153)
            ·
              refine ⟨859489428707491523502115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1145985904943322031336153 859489428707491523502115)
              ·
                refine ⟨1289234143061237285253173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 859489428707491523502115 1289234143061237285253173)
                ·
                  refine ⟨120865700911990995492485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1289234143061237285253173 120865700911990995492485)
                  ·
                    rfl

theorem cell22_1059233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 1, 5].length) (baseStart_1059233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1059233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1059233 prefixEnd_1059233 := by exact prefixLift 1059233
  have htrace : WordTrace (prefixWord ++ tailWord_1059233) baseStart_1059233 baseEnd_1059233 := by
    simpa [prefixWord, tailWord_1059233, baseEnd_1059233] using wordTrace_append hprefix tailTrace_1059233
  have hstable : (prefixWord ++ tailWord_1059233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059233).length < 2 ^ (prefixWord ++ tailWord_1059233).sum := by decide
  have hdescent : baseEnd_1059233 < baseStart_1059233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059304 : List Nat := [2, 1, 4, 1, 1, 3, 1, 1, 5, 3]
def baseStart_1059304 : Nat := 118140960795 + 1059304 * 2 ^ 59
def prefixEnd_1059304 : Nat := 4983230072969 + 3 ^ 40 * 1059304 * 2
def baseEnd_1059304 : Nat := 362621407486952467952237

theorem tailTrace_1059304 : CollatzResearch.WordTrace tailWord_1059304 prefixEnd_1059304 362621407486952467952237 := by
  unfold tailWord_1059304
  simp only [CollatzResearch.WordTrace]
  refine ⟨19317995477164998782476483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25757327302886665043301977 19317995477164998782476483)
  ·
    refine ⟨28976993215747498173714725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19317995477164998782476483 28976993215747498173714725)
    ·
      refine ⟨5433186227952655907571511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28976993215747498173714725 5433186227952655907571511)
      ·
        refine ⟨8149779341928983861357267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5433186227952655907571511 8149779341928983861357267)
        ·
          refine ⟨12224669012893475792035901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8149779341928983861357267 12224669012893475792035901)
          ·
            refine ⟨4584250879835053422013463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12224669012893475792035901 4584250879835053422013463)
            ·
              refine ⟨6876376319752580133020195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4584250879835053422013463 6876376319752580133020195)
              ·
                refine ⟨10314564479628870199530293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6876376319752580133020195 10314564479628870199530293)
                ·
                  refine ⟨966990419965206581205965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10314564479628870199530293 966990419965206581205965)
                  ·
                    refine ⟨362621407486952467952237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 966990419965206581205965 362621407486952467952237)
                    ·
                      rfl

theorem cell22_1059304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_1059304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1059304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1059304 prefixEnd_1059304 := by exact prefixLift 1059304
  have htrace : WordTrace (prefixWord ++ tailWord_1059304) baseStart_1059304 baseEnd_1059304 := by
    simpa [prefixWord, tailWord_1059304, baseEnd_1059304] using wordTrace_append hprefix tailTrace_1059304
  have hstable : (prefixWord ++ tailWord_1059304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059304).length < 2 ^ (prefixWord ++ tailWord_1059304).sum := by decide
  have hdescent : baseEnd_1059304 < baseStart_1059304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059321 : List Nat := [1, 2, 1, 3, 1, 2, 3, 5, 1, 3]
def baseStart_1059321 : Nat := 118140960795 + 1059321 * 2 ^ 59
def prefixEnd_1059321 : Nat := 4983230072969 + 3 ^ 40 * 1059321 * 2
def baseEnd_1059321 : Nat := 362627226934370090277185

theorem tailTrace_1059321 : CollatzResearch.WordTrace tailWord_1059321 prefixEnd_1059321 362627226934370090277185 := by
  unfold tailWord_1059321
  simp only [CollatzResearch.WordTrace]
  refine ⟨38636610995268409468321817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25757740663512272978881211 38636610995268409468321817)
  ·
    refine ⟨28977458246451307101241363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38636610995268409468321817 28977458246451307101241363)
    ·
      refine ⟨43466187369676960651862045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28977458246451307101241363 43466187369676960651862045)
      ·
        refine ⟨16299820263628860244448267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43466187369676960651862045 16299820263628860244448267)
        ·
          refine ⟨24449730395443290366672401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16299820263628860244448267 24449730395443290366672401)
          ·
            refine ⟨18337297796582467775004301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24449730395443290366672401 18337297796582467775004301)
            ·
              refine ⟨6876486673718425415626613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18337297796582467775004301 6876486673718425415626613)
              ·
                refine ⟨644670625661102382714995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6876486673718425415626613 644670625661102382714995)
                ·
                  refine ⟨967005938491653574072493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 644670625661102382714995 967005938491653574072493)
                  ·
                    refine ⟨362627226934370090277185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 967005938491653574072493 362627226934370090277185)
                    ·
                      rfl

theorem cell22_1059321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 5, 1, 3].length) (baseStart_1059321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1059321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1059321 prefixEnd_1059321 := by exact prefixLift 1059321
  have htrace : WordTrace (prefixWord ++ tailWord_1059321) baseStart_1059321 baseEnd_1059321 := by
    simpa [prefixWord, tailWord_1059321, baseEnd_1059321] using wordTrace_append hprefix tailTrace_1059321
  have hstable : (prefixWord ++ tailWord_1059321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059321).length < 2 ^ (prefixWord ++ tailWord_1059321).sum := by decide
  have hdescent : baseEnd_1059321 < baseStart_1059321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059407 : List Nat := [1, 1, 2, 1, 1, 2, 5, 9]
def baseStart_1059407 : Nat := 118140960795 + 1059407 * 2 ^ 59
def prefixEnd_1059407 : Nat := 4983230072969 + 3 ^ 40 * 1059407 * 2
def baseEnd_1059407 : Nat := 40295185165766059180769

theorem tailTrace_1059407 : CollatzResearch.WordTrace tailWord_1059407 prefixEnd_1059407 40295185165766059180769 := by
  unfold tailWord_1059407
  simp only [CollatzResearch.WordTrace]
  refine ⟨38639747672956846155952475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25759831781971230770634983 38639747672956846155952475)
  ·
    refine ⟨57959621509435269233928713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38639747672956846155952475 57959621509435269233928713)
    ·
      refine ⟨43469716132076451925446535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57959621509435269233928713 43469716132076451925446535)
      ·
        refine ⟨65204574198114677888169803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43469716132076451925446535 65204574198114677888169803)
        ·
          refine ⟨97806861297172016832254705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65204574198114677888169803 97806861297172016832254705)
          ·
            refine ⟨73355145972879012624191029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97806861297172016832254705 73355145972879012624191029)
            ·
              refine ⟨6877044934957407433517909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 73355145972879012624191029 6877044934957407433517909)
              ·
                refine ⟨40295185165766059180769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6877044934957407433517909 40295185165766059180769)
                ·
                  rfl

theorem cell22_1059407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 9].length) (baseStart_1059407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1059407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1059407 prefixEnd_1059407 := by exact prefixLift 1059407
  have htrace : WordTrace (prefixWord ++ tailWord_1059407) baseStart_1059407 baseEnd_1059407 := by
    simpa [prefixWord, tailWord_1059407, baseEnd_1059407] using wordTrace_append hprefix tailTrace_1059407
  have hstable : (prefixWord ++ tailWord_1059407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059407).length < 2 ^ (prefixWord ++ tailWord_1059407).sum := by decide
  have hdescent : baseEnd_1059407 < baseStart_1059407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059445 : List Nat := [1, 3, 4, 2, 2, 1, 2, 2, 2, 3]
def baseStart_1059445 : Nat := 118140960795 + 1059445 * 2 ^ 59
def prefixEnd_1059445 : Nat := 4983230072969 + 3 ^ 40 * 1059445 * 2
def baseEnd_1059445 : Nat := 362669674668475100176805

theorem tailTrace_1059445 : CollatzResearch.WordTrace tailWord_1059445 prefixEnd_1059445 362669674668475100176805 := by
  unfold tailWord_1059445
  simp only [CollatzResearch.WordTrace]
  refine ⟨38641133646819178645835789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25760755764546119097223859 38641133646819178645835789)
  ·
    refine ⟨14490425117557191992188421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38641133646819178645835789 14490425117557191992188421)
    ·
      refine ⟨2716954709541973498535329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14490425117557191992188421 2716954709541973498535329)
      ·
        refine ⟨2037716032156480123901497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2716954709541973498535329 2037716032156480123901497)
        ·
          refine ⟨1528287024117360092926123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2037716032156480123901497 1528287024117360092926123)
          ·
            refine ⟨2292430536176040139389185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1528287024117360092926123 2292430536176040139389185)
            ·
              refine ⟨1719322902132030104541889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2292430536176040139389185 1719322902132030104541889)
              ·
                refine ⟨1289492176599022578406417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1719322902132030104541889 1289492176599022578406417)
                ·
                  refine ⟨967119132449266933804813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1289492176599022578406417 967119132449266933804813)
                  ·
                    refine ⟨362669674668475100176805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 967119132449266933804813 362669674668475100176805)
                    ·
                      rfl

theorem cell22_1059445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_1059445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1059445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1059445 prefixEnd_1059445 := by exact prefixLift 1059445
  have htrace : WordTrace (prefixWord ++ tailWord_1059445) baseStart_1059445 baseEnd_1059445 := by
    simpa [prefixWord, tailWord_1059445, baseEnd_1059445] using wordTrace_append hprefix tailTrace_1059445
  have hstable : (prefixWord ++ tailWord_1059445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059445).length < 2 ^ (prefixWord ++ tailWord_1059445).sum := by decide
  have hdescent : baseEnd_1059445 < baseStart_1059445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059486 : List Nat := [4, 3, 1, 1, 1, 1, 2, 2, 7]
def baseStart_1059486 : Nat := 118140960795 + 1059486 * 2 ^ 59
def prefixEnd_1059486 : Nat := 4983230072969 + 3 ^ 40 * 1059486 * 2
def baseEnd_1059486 : Nat := 120894569935454886633893

theorem tailTrace_1059486 : CollatzResearch.WordTrace tailWord_1059486 prefixEnd_1059486 120894569935454886633893 := by
  unfold tailWord_1059486
  simp only [CollatzResearch.WordTrace]
  refine ⟨4830328629958830331009789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25761752693113761765385541 4830328629958830331009789)
  ·
    refine ⟨1811373236234561374128671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4830328629958830331009789 1811373236234561374128671)
    ·
      refine ⟨2717059854351842061193007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1811373236234561374128671 2717059854351842061193007)
      ·
        refine ⟨4075589781527763091789511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2717059854351842061193007 4075589781527763091789511)
        ·
          refine ⟨6113384672291644637684267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4075589781527763091789511 6113384672291644637684267)
          ·
            refine ⟨9170077008437466956526401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6113384672291644637684267 9170077008437466956526401)
            ·
              refine ⟨6877557756328100217394801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9170077008437466956526401 6877557756328100217394801)
              ·
                refine ⟨5158168317246075163046101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6877557756328100217394801 5158168317246075163046101)
                ·
                  refine ⟨120894569935454886633893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5158168317246075163046101 120894569935454886633893)
                  ·
                    rfl

theorem cell22_1059486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_1059486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1059486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1059486 prefixEnd_1059486 := by exact prefixLift 1059486
  have htrace : WordTrace (prefixWord ++ tailWord_1059486) baseStart_1059486 baseEnd_1059486 := by
    simpa [prefixWord, tailWord_1059486, baseEnd_1059486] using wordTrace_append hprefix tailTrace_1059486
  have hstable : (prefixWord ++ tailWord_1059486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059486).length < 2 ^ (prefixWord ++ tailWord_1059486).sum := by decide
  have hdescent : baseEnd_1059486 < baseStart_1059486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059501 : List Nat := [1, 5, 2, 1, 1, 2, 1, 2, 2, 5]
def baseStart_1059501 : Nat := 118140960795 + 1059501 * 2 ^ 59
def prefixEnd_1059501 : Nat := 4983230072969 + 3 ^ 40 * 1059501 * 2
def baseEnd_1059501 : Nat := 362688844612909620776633

theorem tailTrace_1059501 : CollatzResearch.WordTrace tailWord_1059501 prefixEnd_1059501 362688844612909620776633 := by
  unfold tailWord_1059501
  simp only [CollatzResearch.WordTrace]
  refine ⟨38643176134616300209874357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25762117423077533473249571 38643176134616300209874357)
  ·
    refine ⟨3622797762620278144675721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38643176134616300209874357 3622797762620278144675721)
    ·
      refine ⟨2717098321965208608506791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3622797762620278144675721 2717098321965208608506791)
      ·
        refine ⟨4075647482947812912760187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2717098321965208608506791 4075647482947812912760187)
        ·
          refine ⟨6113471224421719369140281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4075647482947812912760187 6113471224421719369140281)
          ·
            refine ⟨4585103418316289526855211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6113471224421719369140281 4585103418316289526855211)
            ·
              refine ⟨6877655127474434290282817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4585103418316289526855211 6877655127474434290282817)
              ·
                refine ⟨5158241345605825717712113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6877655127474434290282817 5158241345605825717712113)
                ·
                  refine ⟨3868681009204369288284085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5158241345605825717712113 3868681009204369288284085)
                  ·
                    refine ⟨362688844612909620776633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3868681009204369288284085 362688844612909620776633)
                    ·
                      rfl

theorem cell22_1059501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_1059501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1059501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1059501 prefixEnd_1059501 := by exact prefixLift 1059501
  have htrace : WordTrace (prefixWord ++ tailWord_1059501) baseStart_1059501 baseEnd_1059501 := by
    simpa [prefixWord, tailWord_1059501, baseEnd_1059501] using wordTrace_append hprefix tailTrace_1059501
  have hstable : (prefixWord ++ tailWord_1059501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059501).length < 2 ^ (prefixWord ++ tailWord_1059501).sum := by decide
  have hdescent : baseEnd_1059501 < baseStart_1059501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059546 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 6, 3]
def baseStart_1059546 : Nat := 118140960795 + 1059546 * 2 ^ 59
def prefixEnd_1059546 : Nat := 4983230072969 + 3 ^ 40 * 1059546 * 2
def baseEnd_1059546 : Nat := 362704249032544503401495

theorem tailTrace_1059546 : CollatzResearch.WordTrace tailWord_1059546 prefixEnd_1059546 362704249032544503401495 := by
  unfold tailWord_1059546
  simp only [CollatzResearch.WordTrace]
  refine ⟨9661204354863318223815623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25763211612968848596841661 9661204354863318223815623)
  ·
    refine ⟨14491806532294977335723435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9661204354863318223815623 14491806532294977335723435)
    ·
      refine ⟨21737709798442466003585153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14491806532294977335723435 21737709798442466003585153)
      ·
        refine ⟨16303282348831849502688865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21737709798442466003585153 16303282348831849502688865)
        ·
          refine ⟨12227461761623887127016649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16303282348831849502688865 12227461761623887127016649)
          ·
            refine ⟨9170596321217915345262487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12227461761623887127016649 9170596321217915345262487)
            ·
              refine ⟨13755894481826873017893731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9170596321217915345262487 13755894481826873017893731)
              ·
                refine ⟨20633841722740309526840597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13755894481826873017893731 20633841722740309526840597)
                ·
                  refine ⟨967211330753452009070653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 20633841722740309526840597 967211330753452009070653)
                  ·
                    refine ⟨362704249032544503401495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 967211330753452009070653 362704249032544503401495)
                    ·
                      rfl

theorem cell22_1059546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 6, 3].length) (baseStart_1059546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1059546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1059546 prefixEnd_1059546 := by exact prefixLift 1059546
  have htrace : WordTrace (prefixWord ++ tailWord_1059546) baseStart_1059546 baseEnd_1059546 := by
    simpa [prefixWord, tailWord_1059546, baseEnd_1059546] using wordTrace_append hprefix tailTrace_1059546
  have hstable : (prefixWord ++ tailWord_1059546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059546).length < 2 ^ (prefixWord ++ tailWord_1059546).sum := by decide
  have hdescent : baseEnd_1059546 < baseStart_1059546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059565 : List Nat := [1, 5, 1, 2, 1, 1, 5, 2, 4]
def baseStart_1059565 : Nat := 118140960795 + 1059565 * 2 ^ 59
def prefixEnd_1059565 : Nat := 4983230072969 + 3 ^ 40 * 1059565 * 2
def baseEnd_1059565 : Nat := 120903584373611595725479

theorem tailTrace_1059565 : CollatzResearch.WordTrace tailWord_1059565 prefixEnd_1059565 120903584373611595725479 := by
  unfold tailWord_1059565
  simp only [CollatzResearch.WordTrace]
  refine ⟨38645510406384439140204149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25763673604256292760136099 38645510406384439140204149)
  ·
    refine ⟨3623016600598541169394139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38645510406384439140204149 3623016600598541169394139)
    ·
      refine ⟨5434524900897811754091209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3623016600598541169394139 5434524900897811754091209)
      ·
        refine ⟨4075893675673358815568407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5434524900897811754091209 4075893675673358815568407)
        ·
          refine ⟨6113840513510038223352611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4075893675673358815568407 6113840513510038223352611)
          ·
            refine ⟨9170760770265057335028917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6113840513510038223352611 9170760770265057335028917)
            ·
              refine ⟨859758822212349125158961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9170760770265057335028917 859758822212349125158961)
              ·
                refine ⟨644819116659261843869221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 859758822212349125158961 644819116659261843869221)
                ·
                  refine ⟨120903584373611595725479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 644819116659261843869221 120903584373611595725479)
                  ·
                    rfl

theorem cell22_1059565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_1059565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1059565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1059565 prefixEnd_1059565 := by exact prefixLift 1059565
  have htrace : WordTrace (prefixWord ++ tailWord_1059565) baseStart_1059565 baseEnd_1059565 := by
    simpa [prefixWord, tailWord_1059565, baseEnd_1059565] using wordTrace_append hprefix tailTrace_1059565
  have hstable : (prefixWord ++ tailWord_1059565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059565).length < 2 ^ (prefixWord ++ tailWord_1059565).sum := by decide
  have hdescent : baseEnd_1059565 < baseStart_1059565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059580 : List Nat := [2, 2, 2, 1, 3, 2, 4, 1, 2, 3]
def baseStart_1059580 : Nat := 118140960795 + 1059580 * 2 ^ 59
def prefixEnd_1059580 : Nat := 4983230072969 + 3 ^ 40 * 1059580 * 2
def baseEnd_1059580 : Nat := 362715887927379748051391

theorem tailTrace_1059580 : CollatzResearch.WordTrace tailWord_1059580 prefixEnd_1059580 362715887927379748051391 := by
  unfold tailWord_1059580
  simp only [CollatzResearch.WordTrace]
  refine ⟨19323028750665048351000097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25764038334220064468000129 19323028750665048351000097)
  ·
    refine ⟨14492271562998786263250073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19323028750665048351000097 14492271562998786263250073)
    ·
      refine ⟨10869203672249089697437555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14492271562998786263250073 10869203672249089697437555)
      ·
        refine ⟨16303805508373634546156333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10869203672249089697437555 16303805508373634546156333)
        ·
          refine ⟨6113927065640112954808625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16303805508373634546156333 6113927065640112954808625)
          ·
            refine ⟨4585445299230084716106469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6113927065640112954808625 4585445299230084716106469)
            ·
              refine ⟨859770993605640884269963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4585445299230084716106469 859770993605640884269963)
              ·
                refine ⟨1289656490408461326404945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 859770993605640884269963 1289656490408461326404945)
                ·
                  refine ⟨967242367806345994803709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1289656490408461326404945 967242367806345994803709)
                  ·
                    refine ⟨362715887927379748051391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 967242367806345994803709 362715887927379748051391)
                    ·
                      rfl

theorem cell22_1059580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 1, 2, 3].length) (baseStart_1059580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1059580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1059580 prefixEnd_1059580 := by exact prefixLift 1059580
  have htrace : WordTrace (prefixWord ++ tailWord_1059580) baseStart_1059580 baseEnd_1059580 := by
    simpa [prefixWord, tailWord_1059580, baseEnd_1059580] using wordTrace_append hprefix tailTrace_1059580
  have hstable : (prefixWord ++ tailWord_1059580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059580).length < 2 ^ (prefixWord ++ tailWord_1059580).sum := by decide
  have hdescent : baseEnd_1059580 < baseStart_1059580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059651 : List Nat := [1, 1, 1, 3, 1, 4, 1, 3, 3, 4]
def baseStart_1059651 : Nat := 118140960795 + 1059651 * 2 ^ 59
def prefixEnd_1059651 : Nat := 4983230072969 + 3 ^ 40 * 1059651 * 2
def baseEnd_1059651 : Nat := 362740192678359229526173

theorem tailTrace_1059651 : CollatzResearch.WordTrace tailWord_1059651 prefixEnd_1059651 362740192678359229526173 := by
  unfold tailWord_1059651
  simp only [CollatzResearch.WordTrace]
  refine ⟨38648647084072875827834807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25765764722715250551889871 38648647084072875827834807)
  ·
    refine ⟨57972970626109313741752211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38648647084072875827834807 57972970626109313741752211)
    ·
      refine ⟨86959455939163970612628317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57972970626109313741752211 86959455939163970612628317)
      ·
        refine ⟨32609795977186488979735619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86959455939163970612628317 32609795977186488979735619)
        ·
          refine ⟨48914693965779733469603429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32609795977186488979735619 48914693965779733469603429)
          ·
            refine ⟨9171505118583700025550643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48914693965779733469603429 9171505118583700025550643)
            ·
              refine ⟨13757257677875550038325965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9171505118583700025550643 13757257677875550038325965)
              ·
                refine ⟨5158971629203331264372237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13757257677875550038325965 5158971629203331264372237)
                ·
                  refine ⟨1934614360951249224139589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5158971629203331264372237 1934614360951249224139589)
                  ·
                    refine ⟨362740192678359229526173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1934614360951249224139589 362740192678359229526173)
                    ·
                      rfl

theorem cell22_1059651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 3, 4].length) (baseStart_1059651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1059651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1059651 prefixEnd_1059651 := by exact prefixLift 1059651
  have htrace : WordTrace (prefixWord ++ tailWord_1059651) baseStart_1059651 baseEnd_1059651 := by
    simpa [prefixWord, tailWord_1059651, baseEnd_1059651] using wordTrace_append hprefix tailTrace_1059651
  have hstable : (prefixWord ++ tailWord_1059651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059651).length < 2 ^ (prefixWord ++ tailWord_1059651).sum := by decide
  have hdescent : baseEnd_1059651 < baseStart_1059651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059666 : List Nat := [3, 2, 2, 1, 1, 2, 1, 2, 8]
def baseStart_1059666 : Nat := 118140960795 + 1059666 * 2 ^ 59
def prefixEnd_1059666 : Nat := 4983230072969 + 3 ^ 40 * 1059666 * 2
def baseEnd_1059666 : Nat := 120915109161634730133709

theorem tailTrace_1059666 : CollatzResearch.WordTrace tailWord_1059666 prefixEnd_1059666 120915109161634730133709 := by
  unfold tailWord_1059666
  simp only [CollatzResearch.WordTrace]
  refine ⟨9662298544754633347407713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25766129452679022259753901 9662298544754633347407713)
  ·
    refine ⟨7246723908565975010555785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9662298544754633347407713 7246723908565975010555785)
    ·
      refine ⟨5435042931424481257916839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7246723908565975010555785 5435042931424481257916839)
      ·
        refine ⟨8152564397136721886875259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5435042931424481257916839 8152564397136721886875259)
        ·
          refine ⟨12228846595705082830312889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8152564397136721886875259 12228846595705082830312889)
          ·
            refine ⟨9171634946778812122734667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12228846595705082830312889 9171634946778812122734667)
            ·
              refine ⟨13757452420168218184102001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9171634946778812122734667 13757452420168218184102001)
              ·
                refine ⟨10318089315126163638076501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13757452420168218184102001 10318089315126163638076501)
                ·
                  refine ⟨120915109161634730133709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10318089315126163638076501 120915109161634730133709)
                  ·
                    rfl

theorem cell22_1059666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_1059666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1059666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1059666 prefixEnd_1059666 := by exact prefixLift 1059666
  have htrace : WordTrace (prefixWord ++ tailWord_1059666) baseStart_1059666 baseEnd_1059666 := by
    simpa [prefixWord, tailWord_1059666, baseEnd_1059666] using wordTrace_append hprefix tailTrace_1059666
  have hstable : (prefixWord ++ tailWord_1059666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059666).length < 2 ^ (prefixWord ++ tailWord_1059666).sum := by decide
  have hdescent : baseEnd_1059666 < baseStart_1059666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059683 : List Nat := [1, 1, 1, 5, 3, 2, 2, 1, 6]
def baseStart_1059683 : Nat := 118140960795 + 1059683 * 2 ^ 59
def prefixEnd_1059683 : Nat := 4983230072969 + 3 ^ 40 * 1059683 * 2
def baseEnd_1059683 : Nat := 120917048977440604242025

theorem tailTrace_1059683 : CollatzResearch.WordTrace tailWord_1059683 prefixEnd_1059683 120917048977440604242025 := by
  unfold tailWord_1059683
  simp only [CollatzResearch.WordTrace]
  refine ⟨38649814219956945292999703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25766542813304630195333135 38649814219956945292999703)
  ·
    refine ⟨57974721329935417939499555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38649814219956945292999703 57974721329935417939499555)
    ·
      refine ⟨86962081994903126909249333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57974721329935417939499555 86962081994903126909249333)
      ·
        refine ⟨8152695187022168147742125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 86962081994903126909249333 8152695187022168147742125)
        ·
          refine ⟨3057260695133313055403297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8152695187022168147742125 3057260695133313055403297)
          ·
            refine ⟨2292945521349984791552473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3057260695133313055403297 2292945521349984791552473)
            ·
              refine ⟨1719709141012488593664355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2292945521349984791552473 1719709141012488593664355)
              ·
                refine ⟨2579563711518732890496533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1719709141012488593664355 2579563711518732890496533)
                ·
                  refine ⟨120917048977440604242025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2579563711518732890496533 120917048977440604242025)
                  ·
                    rfl

theorem cell22_1059683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 6].length) (baseStart_1059683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1059683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1059683 prefixEnd_1059683 := by exact prefixLift 1059683
  have htrace : WordTrace (prefixWord ++ tailWord_1059683) baseStart_1059683 baseEnd_1059683 := by
    simpa [prefixWord, tailWord_1059683, baseEnd_1059683] using wordTrace_append hprefix tailTrace_1059683
  have hstable : (prefixWord ++ tailWord_1059683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059683).length < 2 ^ (prefixWord ++ tailWord_1059683).sum := by decide
  have hdescent : baseEnd_1059683 < baseStart_1059683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059696 : List Nat := [2, 1, 1, 1, 4, 1, 3, 2, 1, 6]
def baseStart_1059696 : Nat := 118140960795 + 1059696 * 2 ^ 59
def prefixEnd_1059696 : Nat := 4983230072969 + 3 ^ 40 * 1059696 * 2
def baseEnd_1059696 : Nat := 362755597097994112151035

theorem tailTrace_1059696 : CollatzResearch.WordTrace tailWord_1059696 prefixEnd_1059696 362755597097994112151035 := by
  unfold tailWord_1059696
  simp only [CollatzResearch.WordTrace]
  refine ⟨19325144184454924256611471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25766858912606565675481961 19325144184454924256611471)
  ·
    refine ⟨28987716276682386384917207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19325144184454924256611471 28987716276682386384917207)
    ·
      refine ⟨43481574415023579577375811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28987716276682386384917207 43481574415023579577375811)
      ·
        refine ⟨65222361622535369366063717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43481574415023579577375811 65222361622535369366063717)
        ·
          refine ⟨12229192804225381756136947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65222361622535369366063717 12229192804225381756136947)
          ·
            refine ⟨18343789206338072634205421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12229192804225381756136947 18343789206338072634205421)
            ·
              refine ⟨6878920952376777237827033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18343789206338072634205421 6878920952376777237827033)
              ·
                refine ⟨5159190714282582928370275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6878920952376777237827033 5159190714282582928370275)
                ·
                  refine ⟨7738786071423874392555413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5159190714282582928370275 7738786071423874392555413)
                  ·
                    refine ⟨362755597097994112151035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7738786071423874392555413 362755597097994112151035)
                    ·
                      rfl

theorem cell22_1059696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 1, 6].length) (baseStart_1059696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1059696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1059696 prefixEnd_1059696 := by exact prefixLift 1059696
  have htrace : WordTrace (prefixWord ++ tailWord_1059696) baseStart_1059696 baseEnd_1059696 := by
    simpa [prefixWord, tailWord_1059696, baseEnd_1059696] using wordTrace_append hprefix tailTrace_1059696
  have hstable : (prefixWord ++ tailWord_1059696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059696).length < 2 ^ (prefixWord ++ tailWord_1059696).sum := by decide
  have hdescent : baseEnd_1059696 < baseStart_1059696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059698 : List Nat := [3, 2, 1, 2, 1, 1, 5, 1, 1, 5]
def baseStart_1059698 : Nat := 118140960795 + 1059698 * 2 ^ 59
def prefixEnd_1059698 : Nat := 4983230072969 + 3 ^ 40 * 1059698 * 2
def baseEnd_1059698 : Nat := 362756281738866773601029

theorem tailTrace_1059698 : CollatzResearch.WordTrace tailWord_1059698 prefixEnd_1059698 362756281738866773601029 := by
  unfold tailWord_1059698
  simp only [CollatzResearch.WordTrace]
  refine ⟨9662590328725650713698937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25766907543268401903197165 9662590328725650713698937)
  ·
    refine ⟨7246942746544238035274203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9662590328725650713698937 7246942746544238035274203)
    ·
      refine ⟨10870414119816357052911305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7246942746544238035274203 10870414119816357052911305)
      ·
        refine ⟨8152810589862267789683479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10870414119816357052911305 8152810589862267789683479)
        ·
          refine ⟨12229215884793401684525219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8152810589862267789683479 12229215884793401684525219)
          ·
            refine ⟨18343823827190102526787829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12229215884793401684525219 18343823827190102526787829)
            ·
              refine ⟨1719733483799072111886359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18343823827190102526787829 1719733483799072111886359)
              ·
                refine ⟨2579600225698608167829539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1719733483799072111886359 2579600225698608167829539)
                ·
                  refine ⟨3869400338547912251744309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2579600225698608167829539 3869400338547912251744309)
                  ·
                    refine ⟨362756281738866773601029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3869400338547912251744309 362756281738866773601029)
                    ·
                      rfl

theorem cell22_1059698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_1059698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1059698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1059698 prefixEnd_1059698 := by exact prefixLift 1059698
  have htrace : WordTrace (prefixWord ++ tailWord_1059698) baseStart_1059698 baseEnd_1059698 := by
    simpa [prefixWord, tailWord_1059698, baseEnd_1059698] using wordTrace_append hprefix tailTrace_1059698
  have hstable : (prefixWord ++ tailWord_1059698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059698).length < 2 ^ (prefixWord ++ tailWord_1059698).sum := by decide
  have hdescent : baseEnd_1059698 < baseStart_1059698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059702 : List Nat := [5, 1, 1, 3, 1, 2, 2, 2, 1, 4]
def baseStart_1059702 : Nat := 118140960795 + 1059702 * 2 ^ 59
def prefixEnd_1059702 : Nat := 4983230072969 + 3 ^ 40 * 1059702 * 2
def baseEnd_1059702 : Nat := 362757651020612096501017

theorem tailTrace_1059702 : CollatzResearch.WordTrace tailWord_1059702 prefixEnd_1059702 362757651020612096501017 := by
  unfold tailWord_1059702
  simp only [CollatzResearch.WordTrace]
  refine ⟨2415656700430506971121335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25767004804592074358627573 2415656700430506971121335)
  ·
    refine ⟨3623485050645760456682003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2415656700430506971121335 3623485050645760456682003)
    ·
      refine ⟨5435227575968640685023005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3623485050645760456682003 5435227575968640685023005)
      ·
        refine ⟨2038210340988240256883627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5435227575968640685023005 2038210340988240256883627)
        ·
          refine ⟨3057315511482360385325441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2038210340988240256883627 3057315511482360385325441)
          ·
            refine ⟨2292986633611770288994081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3057315511482360385325441 2292986633611770288994081)
            ·
              refine ⟨1719739975208827716745561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2292986633611770288994081 1719739975208827716745561)
              ·
                refine ⟨1289804981406620787559171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1719739975208827716745561 1289804981406620787559171)
                ·
                  refine ⟨1934707472109931181338757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1289804981406620787559171 1934707472109931181338757)
                  ·
                    refine ⟨362757651020612096501017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1934707472109931181338757 362757651020612096501017)
                    ·
                      rfl

theorem cell22_1059702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_1059702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1059702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1059702 prefixEnd_1059702 := by exact prefixLift 1059702
  have htrace : WordTrace (prefixWord ++ tailWord_1059702) baseStart_1059702 baseEnd_1059702 := by
    simpa [prefixWord, tailWord_1059702, baseEnd_1059702] using wordTrace_append hprefix tailTrace_1059702
  have hstable : (prefixWord ++ tailWord_1059702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059702).length < 2 ^ (prefixWord ++ tailWord_1059702).sum := by decide
  have hdescent : baseEnd_1059702 < baseStart_1059702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059734 : List Nat := [5, 3, 1, 1, 1, 3, 1, 1, 6]
def baseStart_1059734 : Nat := 118140960795 + 1059734 * 2 ^ 59
def prefixEnd_1059734 : Nat := 4983230072969 + 3 ^ 40 * 1059734 * 2
def baseEnd_1059734 : Nat := 120922868424858226566973

theorem tailTrace_1059734 : CollatzResearch.WordTrace tailWord_1059734 prefixEnd_1059734 120922868424858226566973 := by
  unfold tailWord_1059734
  simp only [CollatzResearch.WordTrace]
  refine ⟨2415729646423261312694141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25767782895181454002070837 2415729646423261312694141)
  ·
    refine ⟨905898617408722992260303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2415729646423261312694141 905898617408722992260303)
    ·
      refine ⟨1358847926113084488390455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 905898617408722992260303 1358847926113084488390455)
      ·
        refine ⟨2038271889169626732585683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1358847926113084488390455 2038271889169626732585683)
        ·
          refine ⟨3057407833754440098878525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2038271889169626732585683 3057407833754440098878525)
          ·
            refine ⟨1146527937657915037079447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3057407833754440098878525 1146527937657915037079447)
            ·
              refine ⟨1719791906486872555619171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1146527937657915037079447 1719791906486872555619171)
              ·
                refine ⟨2579687859730308833428757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1719791906486872555619171 2579687859730308833428757)
                ·
                  refine ⟨120922868424858226566973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2579687859730308833428757 120922868424858226566973)
                  ·
                    rfl

theorem cell22_1059734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_1059734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1059734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1059734 prefixEnd_1059734 := by exact prefixLift 1059734
  have htrace : WordTrace (prefixWord ++ tailWord_1059734) baseStart_1059734 baseEnd_1059734 := by
    simpa [prefixWord, tailWord_1059734, baseEnd_1059734] using wordTrace_append hprefix tailTrace_1059734
  have hstable : (prefixWord ++ tailWord_1059734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059734).length < 2 ^ (prefixWord ++ tailWord_1059734).sum := by decide
  have hdescent : baseEnd_1059734 < baseStart_1059734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059788 : List Nat := [2, 2, 1, 4, 1, 1, 2, 2, 2, 5]
def baseStart_1059788 : Nat := 118140960795 + 1059788 * 2 ^ 59
def prefixEnd_1059788 : Nat := 4983230072969 + 3 ^ 40 * 1059788 * 2
def baseEnd_1059788 : Nat := 362787090578136538850753

theorem tailTrace_1059788 : CollatzResearch.WordTrace tailWord_1059788 prefixEnd_1059788 362787090578136538850753 := by
  unfold tailWord_1059788
  simp only [CollatzResearch.WordTrace]
  refine ⟨19326821942288274112786009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25769095923051032150381345 19326821942288274112786009)
  ·
    refine ⟨14495116456716205584589507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19326821942288274112786009 14495116456716205584589507)
    ·
      refine ⟨21742674685074308376884261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14495116456716205584589507 21742674685074308376884261)
      ·
        refine ⟨4076751503451432820665799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21742674685074308376884261 4076751503451432820665799)
        ·
          refine ⟨6115127255177149230998699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4076751503451432820665799 6115127255177149230998699)
          ·
            refine ⟨9172690882765723846498049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6115127255177149230998699 9172690882765723846498049)
            ·
              refine ⟨6879518162074292884873537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9172690882765723846498049 6879518162074292884873537)
              ·
                refine ⟨5159638621555719663655153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6879518162074292884873537 5159638621555719663655153)
                ·
                  refine ⟨3869728966166789747741365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5159638621555719663655153 3869728966166789747741365)
                  ·
                    refine ⟨362787090578136538850753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3869728966166789747741365 362787090578136538850753)
                    ·
                      rfl

theorem cell22_1059788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_1059788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1059788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1059788 prefixEnd_1059788 := by exact prefixLift 1059788
  have htrace : WordTrace (prefixWord ++ tailWord_1059788) baseStart_1059788 baseEnd_1059788 := by
    simpa [prefixWord, tailWord_1059788, baseEnd_1059788] using wordTrace_append hprefix tailTrace_1059788
  have hstable : (prefixWord ++ tailWord_1059788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059788).length < 2 ^ (prefixWord ++ tailWord_1059788).sum := by decide
  have hdescent : baseEnd_1059788 < baseStart_1059788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059790 : List Nat := [4, 1, 1, 1, 2, 4, 2, 2, 5]
def baseStart_1059790 : Nat := 118140960795 + 1059790 * 2 ^ 59
def prefixEnd_1059790 : Nat := 4983230072969 + 3 ^ 40 * 1059790 * 2
def baseEnd_1059790 : Nat := 120929258406336400100249

theorem tailTrace_1059790 : CollatzResearch.WordTrace tailWord_1059790 prefixEnd_1059790 120929258406336400100249 := by
  unfold tailWord_1059790
  simp only [CollatzResearch.WordTrace]
  refine ⟨4831714603821162820893103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25769144553712868378096549 4831714603821162820893103)
  ·
    refine ⟨7247571905731744231339655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4831714603821162820893103 7247571905731744231339655)
    ·
      refine ⟨10871357858597616347009483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7247571905731744231339655 10871357858597616347009483)
      ·
        refine ⟨16307036787896424520514225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10871357858597616347009483 16307036787896424520514225)
        ·
          refine ⟨12230277590922318390385669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16307036787896424520514225 12230277590922318390385669)
          ·
            refine ⟨2293177048297934698197313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12230277590922318390385669 2293177048297934698197313)
            ·
              refine ⟨1719882786223451023647985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2293177048297934698197313 1719882786223451023647985)
              ·
                refine ⟨1289912089667588267735989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1719882786223451023647985 1289912089667588267735989)
                ·
                  refine ⟨120929258406336400100249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1289912089667588267735989 120929258406336400100249)
                  ·
                    rfl

theorem cell22_1059790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_1059790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1059790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1059790 prefixEnd_1059790 := by exact prefixLift 1059790
  have htrace : WordTrace (prefixWord ++ tailWord_1059790) baseStart_1059790 baseEnd_1059790 := by
    simpa [prefixWord, tailWord_1059790, baseEnd_1059790] using wordTrace_append hprefix tailTrace_1059790
  have hstable : (prefixWord ++ tailWord_1059790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059790).length < 2 ^ (prefixWord ++ tailWord_1059790).sum := by decide
  have hdescent : baseEnd_1059790 < baseStart_1059790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059794 : List Nat := [3, 2, 2, 3, 1, 2, 1, 4, 1, 3]
def baseStart_1059794 : Nat := 118140960795 + 1059794 * 2 ^ 59
def prefixEnd_1059794 : Nat := 4983230072969 + 3 ^ 40 * 1059794 * 2
def baseEnd_1059794 : Nat := 362789144500754523200735

theorem tailTrace_1059794 : CollatzResearch.WordTrace tailWord_1059794 prefixEnd_1059794 362789144500754523200735 := by
  unfold tailWord_1059794
  simp only [CollatzResearch.WordTrace]
  refine ⟨9663465680638702812572609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25769241815036540833526957 9663465680638702812572609)
  ·
    refine ⟨7247599260479027109429457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9663465680638702812572609 7247599260479027109429457)
    ·
      refine ⟨5435699445359270332072093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7247599260479027109429457 5435699445359270332072093)
      ·
        refine ⟨2038387292009726374527035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5435699445359270332072093 2038387292009726374527035)
        ·
          refine ⟨3057580938014589561790553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2038387292009726374527035 3057580938014589561790553)
          ·
            refine ⟨2293185703510942171342915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3057580938014589561790553 2293185703510942171342915)
            ·
              refine ⟨3439778555266413257014373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2293185703510942171342915 3439778555266413257014373)
              ·
                refine ⟨644958479112452485690195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3439778555266413257014373 644958479112452485690195)
                ·
                  refine ⟨967437718668678728535293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 644958479112452485690195 967437718668678728535293)
                  ·
                    refine ⟨362789144500754523200735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 967437718668678728535293 362789144500754523200735)
                    ·
                      rfl

theorem cell22_1059794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_1059794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1059794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1059794 prefixEnd_1059794 := by exact prefixLift 1059794
  have htrace : WordTrace (prefixWord ++ tailWord_1059794) baseStart_1059794 baseEnd_1059794 := by
    simpa [prefixWord, tailWord_1059794, baseEnd_1059794] using wordTrace_append hprefix tailTrace_1059794
  have hstable : (prefixWord ++ tailWord_1059794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059794).length < 2 ^ (prefixWord ++ tailWord_1059794).sum := by decide
  have hdescent : baseEnd_1059794 < baseStart_1059794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059805 : List Nat := [1, 4, 3, 1, 2, 2, 1, 1, 2, 5]
def baseStart_1059805 : Nat := 118140960795 + 1059805 * 2 ^ 59
def prefixEnd_1059805 : Nat := 4983230072969 + 3 ^ 40 * 1059805 * 2
def baseEnd_1059805 : Nat := 362792910025554161175701

theorem tailTrace_1059805 : CollatzResearch.WordTrace tailWord_1059805 prefixEnd_1059805 362792910025554161175701 := by
  unfold tailWord_1059805
  simp only [CollatzResearch.WordTrace]
  refine ⟨38654263925514960128940869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25769509283676640085960579 38654263925514960128940869)
  ·
    refine ⟨7247674486034055024176413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38654263925514960128940869 7247674486034055024176413)
    ·
      refine ⟨2717877932262770634066155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7247674486034055024176413 2717877932262770634066155)
      ·
        refine ⟨4076816898394155951099233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2717877932262770634066155 4076816898394155951099233)
        ·
          refine ⟨3057612673795616963324425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4076816898394155951099233 3057612673795616963324425)
          ·
            refine ⟨2293209505346712722493319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3057612673795616963324425 2293209505346712722493319)
            ·
              refine ⟨3439814258020069083739979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2293209505346712722493319 3439814258020069083739979)
              ·
                refine ⟨5159721387030103625609969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3439814258020069083739979 5159721387030103625609969)
                ·
                  refine ⟨3869791040272577719207477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5159721387030103625609969 3869791040272577719207477)
                  ·
                    refine ⟨362792910025554161175701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3869791040272577719207477 362792910025554161175701)
                    ·
                      rfl

theorem cell22_1059805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_1059805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1059805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1059805 prefixEnd_1059805 := by exact prefixLift 1059805
  have htrace : WordTrace (prefixWord ++ tailWord_1059805) baseStart_1059805 baseEnd_1059805 := by
    simpa [prefixWord, tailWord_1059805, baseEnd_1059805] using wordTrace_append hprefix tailTrace_1059805
  have hstable : (prefixWord ++ tailWord_1059805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059805).length < 2 ^ (prefixWord ++ tailWord_1059805).sum := by decide
  have hdescent : baseEnd_1059805 < baseStart_1059805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059818 : List Nat := [3, 1, 3, 1, 2, 2, 1, 1, 8]
def baseStart_1059818 : Nat := 118140960795 + 1059818 * 2 ^ 59
def prefixEnd_1059818 : Nat := 4983230072969 + 3 ^ 40 * 1059818 * 2
def baseEnd_1059818 : Nat := 120932453397075486866887

theorem tailTrace_1059818 : CollatzResearch.WordTrace tailWord_1059818 prefixEnd_1059818 120932453397075486866887 := by
  unfold tailWord_1059818
  simp only [CollatzResearch.WordTrace]
  refine ⟨9663684518616965837291027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25769825382978575566109405 9663684518616965837291027)
  ·
    refine ⟨14495526777925448755936541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9663684518616965837291027 14495526777925448755936541)
    ·
      refine ⟨5435822541722043283476203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14495526777925448755936541 5435822541722043283476203)
      ·
        refine ⟨8153733812583064925214305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5435822541722043283476203 8153733812583064925214305)
        ·
          refine ⟨6115300359437298693910729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8153733812583064925214305 6115300359437298693910729)
          ·
            refine ⟨4586475269577974020433047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6115300359437298693910729 4586475269577974020433047)
            ·
              refine ⟨6879712904366961030649571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4586475269577974020433047 6879712904366961030649571)
              ·
                refine ⟨10319569356550441545974357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6879712904366961030649571 10319569356550441545974357)
                ·
                  refine ⟨120932453397075486866887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10319569356550441545974357 120932453397075486866887)
                  ·
                    rfl

theorem cell22_1059818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 8].length) (baseStart_1059818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1059818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1059818 prefixEnd_1059818 := by exact prefixLift 1059818
  have htrace : WordTrace (prefixWord ++ tailWord_1059818) baseStart_1059818 baseEnd_1059818 := by
    simpa [prefixWord, tailWord_1059818, baseEnd_1059818] using wordTrace_append hprefix tailTrace_1059818
  have hstable : (prefixWord ++ tailWord_1059818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059818).length < 2 ^ (prefixWord ++ tailWord_1059818).sum := by decide
  have hdescent : baseEnd_1059818 < baseStart_1059818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059833 : List Nat := [1, 2, 1, 3, 1, 3, 1, 4, 1, 5]
def baseStart_1059833 : Nat := 118140960795 + 1059833 * 2 ^ 59
def prefixEnd_1059833 : Nat := 4983230072969 + 3 ^ 40 * 1059833 * 2
def baseEnd_1059833 : Nat := 362802494997771421475615

theorem tailTrace_1059833 : CollatzResearch.WordTrace tailWord_1059833 prefixEnd_1059833 362802494997771421475615 := by
  unfold tailWord_1059833
  simp only [CollatzResearch.WordTrace]
  refine ⟨38655285169413520910960153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25770190112942347273973435 38655285169413520910960153)
  ·
    refine ⟨28991463877060140683220115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38655285169413520910960153 28991463877060140683220115)
    ·
      refine ⟨43487195815590211024830173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28991463877060140683220115 43487195815590211024830173)
      ·
        refine ⟨16307698430846329134311315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43487195815590211024830173 16307698430846329134311315)
        ·
          refine ⟨24461547646269493701466973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16307698430846329134311315 24461547646269493701466973)
          ·
            refine ⟨9173080367351060138050115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24461547646269493701466973 9173080367351060138050115)
            ·
              refine ⟨13759620551026590207075173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9173080367351060138050115 13759620551026590207075173)
              ·
                refine ⟨2579928853317485663826595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13759620551026590207075173 2579928853317485663826595)
                ·
                  refine ⟨3869893279976228495739893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2579928853317485663826595 3869893279976228495739893)
                  ·
                    refine ⟨362802494997771421475615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3869893279976228495739893 362802494997771421475615)
                    ·
                      rfl

theorem cell22_1059833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 5].length) (baseStart_1059833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1059833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1059833 prefixEnd_1059833 := by exact prefixLift 1059833
  have htrace : WordTrace (prefixWord ++ tailWord_1059833) baseStart_1059833 baseEnd_1059833 := by
    simpa [prefixWord, tailWord_1059833, baseEnd_1059833] using wordTrace_append hprefix tailTrace_1059833
  have hstable : (prefixWord ++ tailWord_1059833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059833).length < 2 ^ (prefixWord ++ tailWord_1059833).sum := by decide
  have hdescent : baseEnd_1059833 < baseStart_1059833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059893 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 1, 8]
def baseStart_1059893 : Nat := 118140960795 + 1059893 * 2 ^ 59
def prefixEnd_1059893 : Nat := 4983230072969 + 3 ^ 40 * 1059893 * 2
def baseEnd_1059893 : Nat := 362823034223951264975431

theorem tailTrace_1059893 : CollatzResearch.WordTrace tailWord_1059893 prefixEnd_1059893 362823034223951264975431 := by
  unfold tailWord_1059893
  simp only [CollatzResearch.WordTrace]
  refine ⟨38657473549196151158144333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25771649032797434105429555 38657473549196151158144333)
  ·
    refine ⟨14496552580948556684304125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38657473549196151158144333 14496552580948556684304125)
    ·
      refine ⟨5436207217855708756614047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14496552580948556684304125 5436207217855708756614047)
      ·
        refine ⟨8154310826783563134921071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5436207217855708756614047 8154310826783563134921071)
        ·
          refine ⟨12231466240175344702381607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8154310826783563134921071 12231466240175344702381607)
          ·
            refine ⟨18347199360263017053572411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12231466240175344702381607 18347199360263017053572411)
            ·
              refine ⟨27520799040394525580358617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18347199360263017053572411 27520799040394525580358617)
              ·
                refine ⟨20640599280295894185268963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27520799040394525580358617 20640599280295894185268963)
                ·
                  refine ⟨30960898920443841277903445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20640599280295894185268963 30960898920443841277903445)
                  ·
                    refine ⟨362823034223951264975431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 30960898920443841277903445 362823034223951264975431)
                    ·
                      rfl

theorem cell22_1059893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_1059893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1059893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1059893 prefixEnd_1059893 := by exact prefixLift 1059893
  have htrace : WordTrace (prefixWord ++ tailWord_1059893) baseStart_1059893 baseEnd_1059893 := by
    simpa [prefixWord, tailWord_1059893, baseEnd_1059893] using wordTrace_append hprefix tailTrace_1059893
  have hstable : (prefixWord ++ tailWord_1059893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059893).length < 2 ^ (prefixWord ++ tailWord_1059893).sum := by decide
  have hdescent : baseEnd_1059893 < baseStart_1059893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059925 : List Nat := [1, 3, 2, 2, 1, 2, 3, 3, 5]
def baseStart_1059925 : Nat := 118140960795 + 1059925 * 2 ^ 59
def prefixEnd_1059925 : Nat := 4983230072969 + 3 ^ 40 * 1059925 * 2
def baseEnd_1059925 : Nat := 120944662825971282725111

theorem tailTrace_1059925 : CollatzResearch.WordTrace tailWord_1059925 prefixEnd_1059925 120944662825971282725111 := by
  unfold tailWord_1059925
  simp only [CollatzResearch.WordTrace]
  refine ⟨38658640685080220623309229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25772427123386813748872819 38658640685080220623309229)
  ·
    refine ⟨14496990256905082733740961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38658640685080220623309229 14496990256905082733740961)
    ·
      refine ⟨10872742692678812050305721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14496990256905082733740961 10872742692678812050305721)
      ·
        refine ⟨8154557019509109037729291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10872742692678812050305721 8154557019509109037729291)
        ·
          refine ⟨12231835529263663556593937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8154557019509109037729291 12231835529263663556593937)
          ·
            refine ⟨9173876646947747667445453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12231835529263663556593937 9173876646947747667445453)
            ·
              refine ⟨3440203742605405375292045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9173876646947747667445453 3440203742605405375292045)
              ·
                refine ⟨1290076403477027015734517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3440203742605405375292045 1290076403477027015734517)
                ·
                  refine ⟨120944662825971282725111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1290076403477027015734517 120944662825971282725111)
                  ·
                    rfl

theorem cell22_1059925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 3, 5].length) (baseStart_1059925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1059925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1059925 prefixEnd_1059925 := by exact prefixLift 1059925
  have htrace : WordTrace (prefixWord ++ tailWord_1059925) baseStart_1059925 baseEnd_1059925 := by
    simpa [prefixWord, tailWord_1059925, baseEnd_1059925] using wordTrace_append hprefix tailTrace_1059925
  have hstable : (prefixWord ++ tailWord_1059925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059925).length < 2 ^ (prefixWord ++ tailWord_1059925).sum := by decide
  have hdescent : baseEnd_1059925 < baseStart_1059925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059953 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 10]
def baseStart_1059953 : Nat := 118140960795 + 1059953 * 2 ^ 59
def prefixEnd_1059953 : Nat := 4983230072969 + 3 ^ 40 * 1059953 * 2
def baseEnd_1059953 : Nat := 120947857816710369491749

theorem tailTrace_1059953 : CollatzResearch.WordTrace tailWord_1059953 prefixEnd_1059953 120947857816710369491749 := by
  unfold tailWord_1059953
  simp only [CollatzResearch.WordTrace]
  refine ⟨38659661928978781405328513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25773107952652520936885675 38659661928978781405328513)
  ·
    refine ⟨28994746446734086053996385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38659661928978781405328513 28994746446734086053996385)
    ·
      refine ⟨21746059835050564540497289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28994746446734086053996385 21746059835050564540497289)
      ·
        refine ⟨16309544876287923405372967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21746059835050564540497289 16309544876287923405372967)
        ·
          refine ⟨24464317314431885108059451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16309544876287923405372967 24464317314431885108059451)
          ·
            refine ⟨36696475971647827662089177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24464317314431885108059451 36696475971647827662089177)
            ·
              refine ⟨27522356978735870746566883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36696475971647827662089177 27522356978735870746566883)
              ·
                refine ⟨41283535468103806119850325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27522356978735870746566883 41283535468103806119850325)
                ·
                  refine ⟨120947857816710369491749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 41283535468103806119850325 120947857816710369491749)
                  ·
                    rfl

theorem cell22_1059953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 10].length) (baseStart_1059953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1059953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1059953 prefixEnd_1059953 := by exact prefixLift 1059953
  have htrace : WordTrace (prefixWord ++ tailWord_1059953) baseStart_1059953 baseEnd_1059953 := by
    simpa [prefixWord, tailWord_1059953, baseEnd_1059953] using wordTrace_append hprefix tailTrace_1059953
  have hstable : (prefixWord ++ tailWord_1059953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059953).length < 2 ^ (prefixWord ++ tailWord_1059953).sum := by decide
  have hdescent : baseEnd_1059953 < baseStart_1059953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059983 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 2, 10]
def baseStart_1059983 : Nat := 118140960795 + 1059983 * 2 ^ 59
def prefixEnd_1059983 : Nat := 4983230072969 + 3 ^ 40 * 1059983 * 2
def baseEnd_1059983 : Nat := 362853843063221030225155

theorem tailTrace_1059983 : CollatzResearch.WordTrace tailWord_1059983 prefixEnd_1059983 362853843063221030225155 := by
  unfold tailWord_1059983
  simp only [CollatzResearch.WordTrace]
  refine ⟨38660756118870096528920603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25773837412580064352613735 38660756118870096528920603)
  ·
    refine ⟨57991134178305144793380905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38660756118870096528920603 57991134178305144793380905)
    ·
      refine ⟨43493350633728858595035679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57991134178305144793380905 43493350633728858595035679)
      ·
        refine ⟨65240025950593287892553519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43493350633728858595035679 65240025950593287892553519)
        ·
          refine ⟨97860038925889931838830279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65240025950593287892553519 97860038925889931838830279)
          ·
            refine ⟨146790058388834897758245419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97860038925889931838830279 146790058388834897758245419)
            ·
              refine ⟨220185087583252346637368129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146790058388834897758245419 220185087583252346637368129)
              ·
                refine ⟨165138815687439259978026097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 220185087583252346637368129 165138815687439259978026097)
                ·
                  refine ⟨123854111765579444983519573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 165138815687439259978026097 123854111765579444983519573)
                  ·
                    refine ⟨362853843063221030225155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 123854111765579444983519573 362853843063221030225155)
                    ·
                      rfl

theorem cell22_1059983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 10].length) (baseStart_1059983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1059983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1059983 prefixEnd_1059983 := by exact prefixLift 1059983
  have htrace : WordTrace (prefixWord ++ tailWord_1059983) baseStart_1059983 baseEnd_1059983 := by
    simpa [prefixWord, tailWord_1059983, baseEnd_1059983] using wordTrace_append hprefix tailTrace_1059983
  have hstable : (prefixWord ++ tailWord_1059983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059983).length < 2 ^ (prefixWord ++ tailWord_1059983).sum := by decide
  have hdescent : baseEnd_1059983 < baseStart_1059983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060000 : List Nat := [2, 1, 1, 4, 2, 1, 3, 1, 1, 6]
def baseStart_1060000 : Nat := 118140960795 + 1060000 * 2 ^ 59
def prefixEnd_1060000 : Nat := 4983230072969 + 3 ^ 40 * 1060000 * 2
def baseEnd_1060000 : Nat := 362859662510638652550103

theorem tailTrace_1060000 : CollatzResearch.WordTrace tailWord_1060000 prefixEnd_1060000 362859662510638652550103 := by
  unfold tailWord_1060000
  simp only [CollatzResearch.WordTrace]
  refine ⟨19330688079904254216144727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25774250773205672288192969 19330688079904254216144727)
  ·
    refine ⟨28996032119856381324217091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19330688079904254216144727 28996032119856381324217091)
    ·
      refine ⟨43494048179784571986325637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28996032119856381324217091 43494048179784571986325637)
      ·
        refine ⟨8155134033709607247436057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43494048179784571986325637 8155134033709607247436057)
        ·
          refine ⟨6116350525282205435577043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8155134033709607247436057 6116350525282205435577043)
          ·
            refine ⟨9174525787923308153365565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6116350525282205435577043 9174525787923308153365565)
            ·
              refine ⟨3440447170471240557512087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9174525787923308153365565 3440447170471240557512087)
              ·
                refine ⟨5160670755706860836268131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3440447170471240557512087 5160670755706860836268131)
                ·
                  refine ⟨7741006133560291254402197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5160670755706860836268131 7741006133560291254402197)
                  ·
                    refine ⟨362859662510638652550103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7741006133560291254402197 362859662510638652550103)
                    ·
                      rfl

theorem cell22_1060000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 1, 6].length) (baseStart_1060000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1060000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1060000 prefixEnd_1060000 := by exact prefixLift 1060000
  have htrace : WordTrace (prefixWord ++ tailWord_1060000) baseStart_1060000 baseEnd_1060000 := by
    simpa [prefixWord, tailWord_1060000, baseEnd_1060000] using wordTrace_append hprefix tailTrace_1060000
  have hstable : (prefixWord ++ tailWord_1060000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060000).length < 2 ^ (prefixWord ++ tailWord_1060000).sum := by decide
  have hdescent : baseEnd_1060000 < baseStart_1060000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060004 : List Nat := [2, 3, 1, 2, 3, 2, 2, 3, 4]
def baseStart_1060004 : Nat := 118140960795 + 1060004 * 2 ^ 59
def prefixEnd_1060004 : Nat := 4983230072969 + 3 ^ 40 * 1060004 * 2
def baseEnd_1060004 : Nat := 120953677264127991816697

theorem tailTrace_1060004 : CollatzResearch.WordTrace tailWord_1060004 prefixEnd_1060004 120953677264127991816697 := by
  unfold tailWord_1060004
  simp only [CollatzResearch.WordTrace]
  refine ⟨19330761025897008557717533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25774348034529344743623377 19330761025897008557717533)
  ·
    refine ⟨7249035384711378209144075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19330761025897008557717533 7249035384711378209144075)
    ·
      refine ⟨10873553077067067313716113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7249035384711378209144075 10873553077067067313716113)
      ·
        refine ⟨8155164807800300485287085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10873553077067067313716113 8155164807800300485287085)
        ·
          refine ⟨3058186802925112681982657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8155164807800300485287085 3058186802925112681982657)
          ·
            refine ⟨2293640102193834511486993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3058186802925112681982657 2293640102193834511486993)
            ·
              refine ⟨1720230076645375883615245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2293640102193834511486993 1720230076645375883615245)
              ·
                refine ⟨645086278742015956355717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1720230076645375883615245 645086278742015956355717)
                ·
                  refine ⟨120953677264127991816697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 645086278742015956355717 120953677264127991816697)
                  ·
                    rfl

theorem cell22_1060004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 3, 4].length) (baseStart_1060004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1060004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1060004 prefixEnd_1060004 := by exact prefixLift 1060004
  have htrace : WordTrace (prefixWord ++ tailWord_1060004) baseStart_1060004 baseEnd_1060004 := by
    simpa [prefixWord, tailWord_1060004, baseEnd_1060004] using wordTrace_append hprefix tailTrace_1060004
  have hstable : (prefixWord ++ tailWord_1060004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060004).length < 2 ^ (prefixWord ++ tailWord_1060004).sum := by decide
  have hdescent : baseEnd_1060004 < baseStart_1060004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060036 : List Nat := [2, 3, 3, 1, 4, 1, 1, 1, 1, 5]
def baseStart_1060036 : Nat := 118140960795 + 1060036 * 2 ^ 59
def prefixEnd_1060036 : Nat := 4983230072969 + 3 ^ 40 * 1060036 * 2
def baseEnd_1060036 : Nat := 362871986046346558649993

theorem tailTrace_1060036 : CollatzResearch.WordTrace tailWord_1060036 prefixEnd_1060036 362871986046346558649993 := by
  unfold tailWord_1060036
  simp only [CollatzResearch.WordTrace]
  refine ⟨19331344593839043290299981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25775126125118724387066641 19331344593839043290299981)
  ·
    refine ⟨7249254222689641233862493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19331344593839043290299981 7249254222689641233862493)
    ·
      refine ⟨2718470333508615462698435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7249254222689641233862493 2718470333508615462698435)
      ·
        refine ⟨4077705500262923194047653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2718470333508615462698435 4077705500262923194047653)
        ·
          refine ⟨764569781299298098883935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4077705500262923194047653 764569781299298098883935)
          ·
            refine ⟨1146854671948947148325903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 764569781299298098883935 1146854671948947148325903)
            ·
              refine ⟨1720282007923420722488855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1146854671948947148325903 1720282007923420722488855)
              ·
                refine ⟨2580423011885131083733283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1720282007923420722488855 2580423011885131083733283)
                ·
                  refine ⟨3870634517827696625599925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2580423011885131083733283 3870634517827696625599925)
                  ·
                    refine ⟨362871986046346558649993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3870634517827696625599925 362871986046346558649993)
                    ·
                      rfl

theorem cell22_1060036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_1060036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1060036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1060036 prefixEnd_1060036 := by exact prefixLift 1060036
  have htrace : WordTrace (prefixWord ++ tailWord_1060036) baseStart_1060036 baseEnd_1060036 := by
    simpa [prefixWord, tailWord_1060036, baseEnd_1060036] using wordTrace_append hprefix tailTrace_1060036
  have hstable : (prefixWord ++ tailWord_1060036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060036).length < 2 ^ (prefixWord ++ tailWord_1060036).sum := by decide
  have hdescent : baseEnd_1060036 < baseStart_1060036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060077 : List Nat := [1, 5, 1, 2, 2, 1, 2, 1, 7]
def baseStart_1060077 : Nat := 118140960795 + 1060077 * 2 ^ 59
def prefixEnd_1060077 : Nat := 4983230072969 + 3 ^ 40 * 1060077 * 2
def baseEnd_1060077 : Nat := 120962007061412039458289

theorem tailTrace_1060077 : CollatzResearch.WordTrace tailWord_1060077 prefixEnd_1060077 120962007061412039458289 := by
  unfold tailWord_1060077
  simp only [CollatzResearch.WordTrace]
  refine ⟨38664184580529550582842485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25776123053686367055228323 38664184580529550582842485)
  ·
    refine ⟨3624767304424645367141483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38664184580529550582842485 3624767304424645367141483)
    ·
      refine ⟨5437150956636968050712225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3624767304424645367141483 5437150956636968050712225)
      ·
        refine ⟨4077863217477726038034169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5437150956636968050712225 4077863217477726038034169)
        ·
          refine ⟨3058397413108294528525627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4077863217477726038034169 3058397413108294528525627)
          ·
            refine ⟨4587596119662441792788441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3058397413108294528525627 4587596119662441792788441)
            ·
              refine ⟨3440697089746831344591331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4587596119662441792788441 3440697089746831344591331)
              ·
                refine ⟨5161045634620247016886997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3440697089746831344591331 5161045634620247016886997)
                ·
                  refine ⟨120962007061412039458289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5161045634620247016886997 120962007061412039458289)
                  ·
                    rfl

theorem cell22_1060077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_1060077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1060077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1060077 prefixEnd_1060077 := by exact prefixLift 1060077
  have htrace : WordTrace (prefixWord ++ tailWord_1060077) baseStart_1060077 baseEnd_1060077 := by
    simpa [prefixWord, tailWord_1060077, baseEnd_1060077] using wordTrace_append hprefix tailTrace_1060077
  have hstable : (prefixWord ++ tailWord_1060077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060077).length < 2 ^ (prefixWord ++ tailWord_1060077).sum := by decide
  have hdescent : baseEnd_1060077 < baseStart_1060077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060094 : List Nat := [4, 2, 2, 1, 1, 3, 1, 3, 5]
def baseStart_1060094 : Nat := 118140960795 + 1060094 * 2 ^ 59
def prefixEnd_1060094 : Nat := 4983230072969 + 3 ^ 40 * 1060094 * 2
def baseEnd_1060094 : Nat := 120963946877217913566605

theorem tailTrace_1060094 : CollatzResearch.WordTrace tailWord_1060094 prefixEnd_1060094 120963946877217913566605 := by
  unfold tailWord_1060094
  simp only [CollatzResearch.WordTrace]
  refine ⟨4833100577683495310776417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25776536414311974990807557 4833100577683495310776417)
  ·
    refine ⟨3624825433262621483082313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4833100577683495310776417 3624825433262621483082313)
    ·
      refine ⟨2718619074946966112311735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3624825433262621483082313 2718619074946966112311735)
      ·
        refine ⟨4077928612420449168467603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2718619074946966112311735 4077928612420449168467603)
        ·
          refine ⟨6116892918630673752701405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4077928612420449168467603 6116892918630673752701405)
          ·
            refine ⟨2293834844486502657263027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6116892918630673752701405 2293834844486502657263027)
            ·
              refine ⟨3440752266729753985894541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2293834844486502657263027 3440752266729753985894541)
              ·
                refine ⟨1290282100023657744710453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3440752266729753985894541 1290282100023657744710453)
                ·
                  refine ⟨120963946877217913566605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1290282100023657744710453 120963946877217913566605)
                  ·
                    rfl

theorem cell22_1060094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_1060094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1060094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1060094 prefixEnd_1060094 := by exact prefixLift 1060094
  have htrace : WordTrace (prefixWord ++ tailWord_1060094) baseStart_1060094 baseEnd_1060094 := by
    simpa [prefixWord, tailWord_1060094, baseEnd_1060094] using wordTrace_append hprefix tailTrace_1060094
  have hstable : (prefixWord ++ tailWord_1060094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060094).length < 2 ^ (prefixWord ++ tailWord_1060094).sum := by decide
  have hdescent : baseEnd_1060094 < baseStart_1060094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060105 : List Nat := [1, 2, 1, 1, 3, 3, 2, 1, 8]
def baseStart_1060105 : Nat := 118140960795 + 1060105 * 2 ^ 59
def prefixEnd_1060105 : Nat := 4983230072969 + 3 ^ 40 * 1060105 * 2
def baseEnd_1060105 : Nat := 120965202052151126224927

theorem tailTrace_1060105 : CollatzResearch.WordTrace tailWord_1060105 prefixEnd_1060105 120965202052151126224927 := by
  unfold tailWord_1060105
  simp only [CollatzResearch.WordTrace]
  refine ⟨38665205824428111364861769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25776803882952074243241179 38665205824428111364861769)
  ·
    refine ⟨28998904368321083523646327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38665205824428111364861769 28998904368321083523646327)
    ·
      refine ⟨43498356552481625285469491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28998904368321083523646327 43498356552481625285469491)
      ·
        refine ⟨65247534828722437928204237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43498356552481625285469491 65247534828722437928204237)
        ·
          refine ⟨24467825560770914223076589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65247534828722437928204237 24467825560770914223076589)
          ·
            refine ⟨9175434585289092833653721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24467825560770914223076589 9175434585289092833653721)
            ·
              refine ⟨6881575938966819625240291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9175434585289092833653721 6881575938966819625240291)
              ·
                refine ⟨10322363908450229437860437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6881575938966819625240291 10322363908450229437860437)
                ·
                  refine ⟨120965202052151126224927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10322363908450229437860437 120965202052151126224927)
                  ·
                    rfl

theorem cell22_1060105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 8].length) (baseStart_1060105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1060105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1060105 prefixEnd_1060105 := by exact prefixLift 1060105
  have htrace : WordTrace (prefixWord ++ tailWord_1060105) baseStart_1060105 baseEnd_1060105 := by
    simpa [prefixWord, tailWord_1060105, baseEnd_1060105] using wordTrace_append hprefix tailTrace_1060105
  have hstable : (prefixWord ++ tailWord_1060105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060105).length < 2 ^ (prefixWord ++ tailWord_1060105).sum := by decide
  have hdescent : baseEnd_1060105 < baseStart_1060105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060107 : List Nat := [1, 1, 1, 1, 5, 4, 1, 1, 3, 4]
def baseStart_1060107 : Nat := 118140960795 + 1060107 * 2 ^ 59
def prefixEnd_1060107 : Nat := 4983230072969 + 3 ^ 40 * 1060107 * 2
def baseEnd_1060107 : Nat := 362896290797326040124775

theorem tailTrace_1060107 : CollatzResearch.WordTrace tailWord_1060107 prefixEnd_1060107 362896290797326040124775 := by
  unfold tailWord_1060107
  simp only [CollatzResearch.WordTrace]
  refine ⟨38665278770420865706434575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25776852513613910470956383 38665278770420865706434575)
  ·
    refine ⟨57997918155631298559651863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38665278770420865706434575 57997918155631298559651863)
    ·
      refine ⟨86996877233446947839477795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57997918155631298559651863 86996877233446947839477795)
      ·
        refine ⟨130495315850170421759216693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86996877233446947839477795 130495315850170421759216693)
        ·
          refine ⟨12233935860953477039926565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 130495315850170421759216693 12233935860953477039926565)
          ·
            refine ⟨2293862973928776944986231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12233935860953477039926565 2293862973928776944986231)
            ·
              refine ⟨3440794460893165417479347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2293862973928776944986231 3440794460893165417479347)
              ·
                refine ⟨5161191691339748126219021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3440794460893165417479347 5161191691339748126219021)
                ·
                  refine ⟨1935446884252405547332133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5161191691339748126219021 1935446884252405547332133)
                  ·
                    refine ⟨362896290797326040124775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1935446884252405547332133 362896290797326040124775)
                    ·
                      rfl

theorem cell22_1060107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 3, 4].length) (baseStart_1060107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1060107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1060107 prefixEnd_1060107 := by exact prefixLift 1060107
  have htrace : WordTrace (prefixWord ++ tailWord_1060107) baseStart_1060107 baseEnd_1060107 := by
    simpa [prefixWord, tailWord_1060107, baseEnd_1060107] using wordTrace_append hprefix tailTrace_1060107
  have hstable : (prefixWord ++ tailWord_1060107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060107).length < 2 ^ (prefixWord ++ tailWord_1060107).sum := by decide
  have hdescent : baseEnd_1060107 < baseStart_1060107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060154 : List Nat := [3, 1, 1, 1, 4, 1, 1, 5, 2, 3]
def baseStart_1060154 : Nat := 118140960795 + 1060154 * 2 ^ 59
def prefixEnd_1060154 : Nat := 4983230072969 + 3 ^ 40 * 1060154 * 2
def baseEnd_1060154 : Nat := 362912379857833584199631

theorem tailTrace_1060154 : CollatzResearch.WordTrace tailWord_1060154 prefixEnd_1060154 362912379857833584199631 := by
  unfold tailWord_1060154
  simp only [CollatzResearch.WordTrace]
  refine ⟨9666748250312648183348879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25777995334167061822263677 9666748250312648183348879)
  ·
    refine ⟨14500122375468972275023319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9666748250312648183348879 14500122375468972275023319)
    ·
      refine ⟨21750183563203458412534979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14500122375468972275023319 21750183563203458412534979)
      ·
        refine ⟨32625275344805187618802469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21750183563203458412534979 32625275344805187618802469)
        ·
          refine ⟨6117239127150972678525463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32625275344805187618802469 6117239127150972678525463)
          ·
            refine ⟨9175858690726459017788195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6117239127150972678525463 9175858690726459017788195)
            ·
              refine ⟨13763788036089688526682293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9175858690726459017788195 13763788036089688526682293)
              ·
                refine ⟨1290355128383408299376465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13763788036089688526682293 1290355128383408299376465)
                ·
                  refine ⟨967766346287556224532349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1290355128383408299376465 967766346287556224532349)
                  ·
                    refine ⟨362912379857833584199631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 967766346287556224532349 362912379857833584199631)
                    ·
                      rfl

theorem cell22_1060154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 5, 2, 3].length) (baseStart_1060154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1060154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1060154 prefixEnd_1060154 := by exact prefixLift 1060154
  have htrace : WordTrace (prefixWord ++ tailWord_1060154) baseStart_1060154 baseEnd_1060154 := by
    simpa [prefixWord, tailWord_1060154, baseEnd_1060154] using wordTrace_append hprefix tailTrace_1060154
  have hstable : (prefixWord ++ tailWord_1060154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060154).length < 2 ^ (prefixWord ++ tailWord_1060154).sum := by decide
  have hdescent : baseEnd_1060154 < baseStart_1060154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060287 : List Nat := [1, 1, 2, 2, 2, 1, 1, 5, 1, 6]
def baseStart_1060287 : Nat := 118140960795 + 1060287 * 2 ^ 59
def prefixEnd_1060287 : Nat := 4983230072969 + 3 ^ 40 * 1060287 * 2
def baseEnd_1060287 : Nat := 362957908475865570624223

theorem tailTrace_1060287 : CollatzResearch.WordTrace tailWord_1060287 prefixEnd_1060287 362957908475865570624223 := by
  unfold tailWord_1060287
  simp only [CollatzResearch.WordTrace]
  refine ⟨38671843909768756447987115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25781229273179170965324743 38671843909768756447987115)
  ·
    refine ⟨58007765864653134671980673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38671843909768756447987115 58007765864653134671980673)
    ·
      refine ⟨43505824398489851003985505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58007765864653134671980673 43505824398489851003985505)
      ·
        refine ⟨32629368298867388252989129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43505824398489851003985505 32629368298867388252989129)
        ·
          refine ⟨24472026224150541189741847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32629368298867388252989129 24472026224150541189741847)
          ·
            refine ⟨36708039336225811784612771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24472026224150541189741847 36708039336225811784612771)
            ·
              refine ⟨55062059004338717676919157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36708039336225811784612771 55062059004338717676919157)
              ·
                refine ⟨5162068031656754782211171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55062059004338717676919157 5162068031656754782211171)
                ·
                  refine ⟨7743102047485132173316757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5162068031656754782211171 7743102047485132173316757)
                  ·
                    refine ⟨362957908475865570624223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7743102047485132173316757 362957908475865570624223)
                    ·
                      rfl

theorem cell22_1060287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 6].length) (baseStart_1060287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1060287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1060287 prefixEnd_1060287 := by exact prefixLift 1060287
  have htrace : WordTrace (prefixWord ++ tailWord_1060287) baseStart_1060287 baseEnd_1060287 := by
    simpa [prefixWord, tailWord_1060287, baseEnd_1060287] using wordTrace_append hprefix tailTrace_1060287
  have hstable : (prefixWord ++ tailWord_1060287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060287).length < 2 ^ (prefixWord ++ tailWord_1060287).sum := by decide
  have hdescent : baseEnd_1060287 < baseStart_1060287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060308 : List Nat := [2, 4, 1, 2, 3, 1, 1, 4, 4]
def baseStart_1060308 : Nat := 118140960795 + 1060308 * 2 ^ 59
def prefixEnd_1060308 : Nat := 4983230072969 + 3 ^ 40 * 1060308 * 2
def baseEnd_1060308 : Nat := 120988365735009505283053

theorem tailTrace_1060308 : CollatzResearch.WordTrace tailWord_1060308 prefixEnd_1060308 120988365735009505283053 := by
  unfold tailWord_1060308
  simp only [CollatzResearch.WordTrace]
  refine ⟨19336304921346338517250789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25781739895128451356334385 19336304921346338517250789)
  ·
    refine ⟨3625557172752438471984523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19336304921346338517250789 3625557172752438471984523)
    ·
      refine ⟨5438335759128657707976785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3625557172752438471984523 5438335759128657707976785)
      ·
        refine ⟨4078751819346493280982589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5438335759128657707976785 4078751819346493280982589)
        ·
          refine ⟨1529531932254934980368471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4078751819346493280982589 1529531932254934980368471)
          ·
            refine ⟨2294297898382402470552707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1529531932254934980368471 2294297898382402470552707)
            ·
              refine ⟨3441446847573603705829061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2294297898382402470552707 3441446847573603705829061)
              ·
                refine ⟨645271283920050694842949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3441446847573603705829061 645271283920050694842949)
                ·
                  refine ⟨120988365735009505283053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 645271283920050694842949 120988365735009505283053)
                  ·
                    rfl

theorem cell22_1060308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_1060308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1060308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1060308 prefixEnd_1060308 := by exact prefixLift 1060308
  have htrace : WordTrace (prefixWord ++ tailWord_1060308) baseStart_1060308 baseEnd_1060308 := by
    simpa [prefixWord, tailWord_1060308, baseEnd_1060308] using wordTrace_append hprefix tailTrace_1060308
  have hstable : (prefixWord ++ tailWord_1060308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060308).length < 2 ^ (prefixWord ++ tailWord_1060308).sum := by decide
  have hdescent : baseEnd_1060308 < baseStart_1060308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060338 : List Nat := [3, 2, 1, 4, 1, 3, 1, 1, 2, 4]
def baseStart_1060338 : Nat := 118140960795 + 1060338 * 2 ^ 59
def prefixEnd_1060338 : Nat := 4983230072969 + 3 ^ 40 * 1060338 * 2
def baseEnd_1060338 : Nat := 362975366818118437599067

theorem tailTrace_1060338 : CollatzResearch.WordTrace tailWord_1060338 prefixEnd_1060338 362975366818118437599067 := by
  unfold tailWord_1060338
  simp only [CollatzResearch.WordTrace]
  refine ⟨9668426008145998039523417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25782469355055994772062445 9668426008145998039523417)
  ·
    refine ⟨7251319506109498529642563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9668426008145998039523417 7251319506109498529642563)
    ·
      refine ⟨10876979259164247794463845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7251319506109498529642563 10876979259164247794463845)
      ·
        refine ⟨2039433611093296461461971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10876979259164247794463845 2039433611093296461461971)
        ·
          refine ⟨3059150416639944692192957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2039433611093296461461971 3059150416639944692192957)
          ·
            refine ⟨1147181406239979259572359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3059150416639944692192957 1147181406239979259572359)
            ·
              refine ⟨1720772109359968889358539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1147181406239979259572359 1720772109359968889358539)
              ·
                refine ⟨2581158164039953334037809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1720772109359968889358539 2581158164039953334037809)
                ·
                  refine ⟨1935868623029965000528357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2581158164039953334037809 1935868623029965000528357)
                  ·
                    refine ⟨362975366818118437599067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1935868623029965000528357 362975366818118437599067)
                    ·
                      rfl

theorem cell22_1060338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 2, 4].length) (baseStart_1060338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1060338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1060338 prefixEnd_1060338 := by exact prefixLift 1060338
  have htrace : WordTrace (prefixWord ++ tailWord_1060338) baseStart_1060338 baseEnd_1060338 := by
    simpa [prefixWord, tailWord_1060338, baseEnd_1060338] using wordTrace_append hprefix tailTrace_1060338
  have hstable : (prefixWord ++ tailWord_1060338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060338).length < 2 ^ (prefixWord ++ tailWord_1060338).sum := by decide
  have hdescent : baseEnd_1060338 < baseStart_1060338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060347 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 9]
def baseStart_1060347 : Nat := 118140960795 + 1060347 * 2 ^ 59
def prefixEnd_1060347 : Nat := 4983230072969 + 3 ^ 40 * 1060347 * 2
def baseEnd_1060347 : Nat := 120992815900681804708013

theorem tailTrace_1060347 : CollatzResearch.WordTrace tailWord_1060347 prefixEnd_1060347 120992815900681804708013 := by
  unfold tailWord_1060347
  simp only [CollatzResearch.WordTrace]
  refine ⟨38674032289551386695171295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25782688193034257796780863 38674032289551386695171295)
  ·
    refine ⟨58011048434327080042756943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38674032289551386695171295 58011048434327080042756943)
    ·
      refine ⟨87016572651490620064135415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58011048434327080042756943 87016572651490620064135415)
      ·
        refine ⟨130524858977235930096203123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87016572651490620064135415 130524858977235930096203123)
        ·
          refine ⟨195787288465853895144304685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130524858977235930096203123 195787288465853895144304685)
          ·
            refine ⟨73420233174695210679114257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 195787288465853895144304685 73420233174695210679114257)
            ·
              refine ⟨55065174881021408009335693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73420233174695210679114257 55065174881021408009335693)
              ·
                refine ⟨20649440580383028003500885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55065174881021408009335693 20649440580383028003500885)
                ·
                  refine ⟨120992815900681804708013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 20649440580383028003500885 120992815900681804708013)
                  ·
                    rfl

theorem cell22_1060347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 9].length) (baseStart_1060347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1060347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1060347 prefixEnd_1060347 := by exact prefixLift 1060347
  have htrace : WordTrace (prefixWord ++ tailWord_1060347) baseStart_1060347 baseEnd_1060347 := by
    simpa [prefixWord, tailWord_1060347, baseEnd_1060347] using wordTrace_append hprefix tailTrace_1060347
  have hstable : (prefixWord ++ tailWord_1060347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060347).length < 2 ^ (prefixWord ++ tailWord_1060347).sum := by decide
  have hdescent : baseEnd_1060347 < baseStart_1060347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060445 : List Nat := [1, 4, 4, 2, 1, 1, 1, 1, 3, 4]
def baseStart_1060445 : Nat := 118140960795 + 1060445 * 2 ^ 59
def prefixEnd_1060445 : Nat := 4983230072969 + 3 ^ 40 * 1060445 * 2
def baseEnd_1060445 : Nat := 363011995104805825173739

theorem tailTrace_1060445 : CollatzResearch.WordTrace tailWord_1060445 prefixEnd_1060445 363011995104805825173739 := by
  unfold tailWord_1060445
  simp only [CollatzResearch.WordTrace]
  refine ⟨38677606643196349432238789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25785071095464232954825859 38677606643196349432238789)
  ·
    refine ⟨7252051245599315518544773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38677606643196349432238789 7252051245599315518544773)
    ·
      refine ⟨1359759608549871659727145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7252051245599315518544773 1359759608549871659727145)
      ·
        refine ⟨1019819706412403744795359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1359759608549871659727145 1019819706412403744795359)
        ·
          refine ⟨1529729559618605617193039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1019819706412403744795359 1529729559618605617193039)
          ·
            refine ⟨2294594339427908425789559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1529729559618605617193039 2294594339427908425789559)
            ·
              refine ⟨3441891509141862638684339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2294594339427908425789559 3441891509141862638684339)
              ·
                refine ⟨5162837263712793958026509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3441891509141862638684339 5162837263712793958026509)
                ·
                  refine ⟨1936063973892297734259941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5162837263712793958026509 1936063973892297734259941)
                  ·
                    refine ⟨363011995104805825173739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1936063973892297734259941 363011995104805825173739)
                    ·
                      rfl

theorem cell22_1060445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_1060445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1060445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1060445 prefixEnd_1060445 := by exact prefixLift 1060445
  have htrace : WordTrace (prefixWord ++ tailWord_1060445) baseStart_1060445 baseEnd_1060445 := by
    simpa [prefixWord, tailWord_1060445, baseEnd_1060445] using wordTrace_append hprefix tailTrace_1060445
  have hstable : (prefixWord ++ tailWord_1060445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060445).length < 2 ^ (prefixWord ++ tailWord_1060445).sum := by decide
  have hdescent : baseEnd_1060445 < baseStart_1060445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060503 : List Nat := [1, 1, 3, 3, 2, 3, 1, 2, 3, 3]
def baseStart_1060503 : Nat := 118140960795 + 1060503 * 2 ^ 59
def prefixEnd_1060503 : Nat := 4983230072969 + 3 ^ 40 * 1060503 * 2
def baseEnd_1060503 : Nat := 363031849690113007223561

theorem tailTrace_1060503 : CollatzResearch.WordTrace tailWord_1060503 prefixEnd_1060503 363031849690113007223561 := by
  unfold tailWord_1060503
  simp only [CollatzResearch.WordTrace]
  refine ⟨38679722076986225337850163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25786481384657483558566775 38679722076986225337850163)
  ·
    refine ⟨58019583115479338006775245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38679722076986225337850163 58019583115479338006775245)
    ·
      refine ⟨21757343668304751752540717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58019583115479338006775245 21757343668304751752540717)
      ·
        refine ⟨8159003875614281907202769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21757343668304751752540717 8159003875614281907202769)
        ·
          refine ⟨6119252906710711430402077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8159003875614281907202769 6119252906710711430402077)
          ·
            refine ⟨2294719840016516786400779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6119252906710711430402077 2294719840016516786400779)
            ·
              refine ⟨3442079760024775179601169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2294719840016516786400779 3442079760024775179601169)
              ·
                refine ⟨2581559820018581384700877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3442079760024775179601169 2581559820018581384700877)
                ·
                  refine ⟨968084932506968019262829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2581559820018581384700877 968084932506968019262829)
                  ·
                    refine ⟨363031849690113007223561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 968084932506968019262829 363031849690113007223561)
                    ·
                      rfl

theorem cell22_1060503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 3, 3].length) (baseStart_1060503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1060503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1060503 prefixEnd_1060503 := by exact prefixLift 1060503
  have htrace : WordTrace (prefixWord ++ tailWord_1060503) baseStart_1060503 baseEnd_1060503 := by
    simpa [prefixWord, tailWord_1060503, baseEnd_1060503] using wordTrace_append hprefix tailTrace_1060503
  have hstable : (prefixWord ++ tailWord_1060503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060503).length < 2 ^ (prefixWord ++ tailWord_1060503).sum := by decide
  have hdescent : baseEnd_1060503 < baseStart_1060503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060533 : List Nat := [1, 3, 3, 3, 2, 1, 1, 1, 7]
def baseStart_1060533 : Nat := 118140960795 + 1060533 * 2 ^ 59
def prefixEnd_1060533 : Nat := 4983230072969 + 3 ^ 40 * 1060533 * 2
def baseEnd_1060533 : Nat := 121014039767734309657823

theorem tailTrace_1060533 : CollatzResearch.WordTrace tailWord_1060533 prefixEnd_1060533 121014039767734309657823 := by
  unfold tailWord_1060533
  simp only [CollatzResearch.WordTrace]
  refine ⟨38680816266877540461442253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25787210844585026974294835 38680816266877540461442253)
  ·
    refine ⟨14505306100079077673040845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38680816266877540461442253 14505306100079077673040845)
    ·
      refine ⟨5439489787529654127390317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14505306100079077673040845 5439489787529654127390317)
      ·
        refine ⟨2039808670323620297771369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5439489787529654127390317 2039808670323620297771369)
        ·
          refine ⟨1529856502742715223328527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2039808670323620297771369 1529856502742715223328527)
          ·
            refine ⟨2294784754114072834992791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1529856502742715223328527 2294784754114072834992791)
            ·
              refine ⟨3442177131171109252489187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2294784754114072834992791 3442177131171109252489187)
              ·
                refine ⟨5163265696756663878733781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3442177131171109252489187 5163265696756663878733781)
                ·
                  refine ⟨121014039767734309657823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5163265696756663878733781 121014039767734309657823)
                  ·
                    rfl

theorem cell22_1060533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 7].length) (baseStart_1060533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1060533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1060533 prefixEnd_1060533 := by exact prefixLift 1060533
  have htrace : WordTrace (prefixWord ++ tailWord_1060533) baseStart_1060533 baseEnd_1060533 := by
    simpa [prefixWord, tailWord_1060533, baseEnd_1060533] using wordTrace_append hprefix tailTrace_1060533
  have hstable : (prefixWord ++ tailWord_1060533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060533).length < 2 ^ (prefixWord ++ tailWord_1060533).sum := by decide
  have hdescent : baseEnd_1060533 < baseStart_1060533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060561 : List Nat := [1, 2, 2, 1, 2, 4, 2, 2, 6]
def baseStart_1060561 : Nat := 118140960795 + 1060561 * 2 ^ 59
def prefixEnd_1060561 : Nat := 4983230072969 + 3 ^ 40 * 1060561 * 2
def baseEnd_1060561 : Nat := 121017234758473396424461

theorem tailTrace_1060561 : CollatzResearch.WordTrace tailWord_1060561 prefixEnd_1060561 121017234758473396424461 := by
  unfold tailWord_1060561
  simp only [CollatzResearch.WordTrace]
  refine ⟨38681837510776101243461537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25787891673850734162307691 38681837510776101243461537)
  ·
    refine ⟨29011378133082075932596153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38681837510776101243461537 29011378133082075932596153)
    ·
      refine ⟨21758533599811556949447115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29011378133082075932596153 21758533599811556949447115)
      ·
        refine ⟨32637800399717335424170673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21758533599811556949447115 32637800399717335424170673)
        ·
          refine ⟨24478350299788001568128005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32637800399717335424170673 24478350299788001568128005)
          ·
            refine ⟨4589690681210250294024001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24478350299788001568128005 4589690681210250294024001)
            ·
              refine ⟨3442268010907687720518001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4589690681210250294024001 3442268010907687720518001)
              ·
                refine ⟨2581701008180765790388501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3442268010907687720518001 2581701008180765790388501)
                ·
                  refine ⟨121017234758473396424461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2581701008180765790388501 121017234758473396424461)
                  ·
                    rfl

theorem cell22_1060561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 6].length) (baseStart_1060561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1060561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1060561 prefixEnd_1060561 := by exact prefixLift 1060561
  have htrace : WordTrace (prefixWord ++ tailWord_1060561) baseStart_1060561 baseEnd_1060561 := by
    simpa [prefixWord, tailWord_1060561, baseEnd_1060561] using wordTrace_append hprefix tailTrace_1060561
  have hstable : (prefixWord ++ tailWord_1060561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060561).length < 2 ^ (prefixWord ++ tailWord_1060561).sum := by decide
  have hdescent : baseEnd_1060561 < baseStart_1060561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060576 : List Nat := [2, 1, 1, 3, 1, 2, 2, 4, 1, 5]
def baseStart_1060576 : Nat := 118140960795 + 1060576 * 2 ^ 59
def prefixEnd_1060576 : Nat := 4983230072969 + 3 ^ 40 * 1060576 * 2
def baseEnd_1060576 : Nat := 363056839081965150148337

theorem tailTrace_1060576 : CollatzResearch.WordTrace tailWord_1060576 prefixEnd_1060576 363056839081965150148337 := by
  unfold tailWord_1060576
  simp only [CollatzResearch.WordTrace]
  refine ⟨19341192302860879402628791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25788256403814505870171721 19341192302860879402628791)
  ·
    refine ⟨29011788454291319103943187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19341192302860879402628791 29011788454291319103943187)
    ·
      refine ⟨43517682681436978655914781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29011788454291319103943187 43517682681436978655914781)
      ·
        refine ⟨16319131005538866995968043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43517682681436978655914781 16319131005538866995968043)
        ·
          refine ⟨24478696508308300493952065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16319131005538866995968043 24478696508308300493952065)
          ·
            refine ⟨18359022381231225370464049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24478696508308300493952065 18359022381231225370464049)
            ·
              refine ⟨13769266785923419027848037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18359022381231225370464049 13769266785923419027848037)
              ·
                refine ⟨2581737522360641067721507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13769266785923419027848037 2581737522360641067721507)
                ·
                  refine ⟨3872606283540961601582261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2581737522360641067721507 3872606283540961601582261)
                  ·
                    refine ⟨363056839081965150148337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3872606283540961601582261 363056839081965150148337)
                    ·
                      rfl

theorem cell22_1060576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 1, 5].length) (baseStart_1060576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1060576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1060576 prefixEnd_1060576 := by exact prefixLift 1060576
  have htrace : WordTrace (prefixWord ++ tailWord_1060576) baseStart_1060576 baseEnd_1060576 := by
    simpa [prefixWord, tailWord_1060576, baseEnd_1060576] using wordTrace_append hprefix tailTrace_1060576
  have hstable : (prefixWord ++ tailWord_1060576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060576).length < 2 ^ (prefixWord ++ tailWord_1060576).sum := by decide
  have hdescent : baseEnd_1060576 < baseStart_1060576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060593 : List Nat := [1, 2, 2, 2, 2, 3, 2, 1, 4, 3]
def baseStart_1060593 : Nat := 118140960795 + 1060593 * 2 ^ 59
def prefixEnd_1060593 : Nat := 4983230072969 + 3 ^ 40 * 1060593 * 2
def baseEnd_1060593 : Nat := 363062658529382772473285

theorem tailTrace_1060593 : CollatzResearch.WordTrace tailWord_1060593 prefixEnd_1060593 363062658529382772473285 := by
  unfold tailWord_1060593
  simp only [CollatzResearch.WordTrace]
  refine ⟨38683004646660170708626433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25788669764440113805750955 38683004646660170708626433)
  ·
    refine ⟨29012253484995128031469825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38683004646660170708626433 29012253484995128031469825)
    ·
      refine ⟨21759190113746346023602369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29012253484995128031469825 21759190113746346023602369)
      ·
        refine ⟨16319392585309759517701777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21759190113746346023602369 16319392585309759517701777)
        ·
          refine ⟨12239544438982319638276333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16319392585309759517701777 12239544438982319638276333)
          ·
            refine ⟨4589829164618369864353625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12239544438982319638276333 4589829164618369864353625)
            ·
              refine ⟨3442371873463777398265219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4589829164618369864353625 3442371873463777398265219)
              ·
                refine ⟨5163557810195666097397829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3442371873463777398265219 5163557810195666097397829)
                ·
                  refine ⟨968167089411687393262093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5163557810195666097397829 968167089411687393262093)
                  ·
                    refine ⟨363062658529382772473285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 968167089411687393262093 363062658529382772473285)
                    ·
                      rfl

theorem cell22_1060593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 4, 3].length) (baseStart_1060593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1060593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1060593 prefixEnd_1060593 := by exact prefixLift 1060593
  have htrace : WordTrace (prefixWord ++ tailWord_1060593) baseStart_1060593 baseEnd_1060593 := by
    simpa [prefixWord, tailWord_1060593, baseEnd_1060593] using wordTrace_append hprefix tailTrace_1060593
  have hstable : (prefixWord ++ tailWord_1060593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060593).length < 2 ^ (prefixWord ++ tailWord_1060593).sum := by decide
  have hdescent : baseEnd_1060593 < baseStart_1060593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060655 : List Nat := [1, 1, 2, 1, 2, 1, 2, 8, 1, 3]
def baseStart_1060655 : Nat := 118140960795 + 1060655 * 2 ^ 59
def prefixEnd_1060655 : Nat := 4983230072969 + 3 ^ 40 * 1060655 * 2
def baseEnd_1060655 : Nat := 363083882396435277423095

theorem tailTrace_1060655 : CollatzResearch.WordTrace tailWord_1060655 prefixEnd_1060655 363083882396435277423095 := by
  unfold tailWord_1060655
  simp only [CollatzResearch.WordTrace]
  refine ⟨38685265972435555297383419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25790177314957036864922279 38685265972435555297383419)
  ·
    refine ⟨58027898958653332946075129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38685265972435555297383419 58027898958653332946075129)
    ·
      refine ⟨43520924218989999709556347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58027898958653332946075129 43520924218989999709556347)
      ·
        refine ⟨65281386328484999564334521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43520924218989999709556347 65281386328484999564334521)
        ·
          refine ⟨48961039746363749673250891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65281386328484999564334521 48961039746363749673250891)
          ·
            refine ⟨73441559619545624509876337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48961039746363749673250891 73441559619545624509876337)
            ·
              refine ⟨55081169714659218382407253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73441559619545624509876337 55081169714659218382407253)
              ·
                refine ⟨645482457593662715418835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 55081169714659218382407253 645482457593662715418835)
                ·
                  refine ⟨968223686390494073128253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 645482457593662715418835 968223686390494073128253)
                  ·
                    refine ⟨363083882396435277423095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 968223686390494073128253 363083882396435277423095)
                    ·
                      rfl

theorem cell22_1060655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 8, 1, 3].length) (baseStart_1060655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1060655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1060655 prefixEnd_1060655 := by exact prefixLift 1060655
  have htrace : WordTrace (prefixWord ++ tailWord_1060655) baseStart_1060655 baseEnd_1060655 := by
    simpa [prefixWord, tailWord_1060655, baseEnd_1060655] using wordTrace_append hprefix tailTrace_1060655
  have hstable : (prefixWord ++ tailWord_1060655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060655).length < 2 ^ (prefixWord ++ tailWord_1060655).sum := by decide
  have hdescent : baseEnd_1060655 < baseStart_1060655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060668 : List Nat := [2, 2, 2, 2, 1, 1, 4, 3, 5]
def baseStart_1060668 : Nat := 118140960795 + 1060668 * 2 ^ 59
def prefixEnd_1060668 : Nat := 4983230072969 + 3 ^ 40 * 1060668 * 2
def baseEnd_1060668 : Nat := 121029444187369192282685

theorem tailTrace_1060668 : CollatzResearch.WordTrace tailWord_1060668 prefixEnd_1060668 121029444187369192282685 := by
  unfold tailWord_1060668
  simp only [CollatzResearch.WordTrace]
  refine ⟨19342870060694229258803329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25790493414258972345071105 19342870060694229258803329)
  ·
    refine ⟨14507152545520671944102497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19342870060694229258803329 14507152545520671944102497)
    ·
      refine ⟨10880364409140503958076873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14507152545520671944102497 10880364409140503958076873)
      ·
        refine ⟨8160273306855377968557655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10880364409140503958076873 8160273306855377968557655)
        ·
          refine ⟨12240409960283066952836483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8160273306855377968557655 12240409960283066952836483)
          ·
            refine ⟨18360614940424600429254725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12240409960283066952836483 18360614940424600429254725)
            ·
              refine ⟨3442615301329612580485261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18360614940424600429254725 3442615301329612580485261)
              ·
                refine ⟨1290980737998604717681973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3442615301329612580485261 1290980737998604717681973)
                ·
                  refine ⟨121029444187369192282685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1290980737998604717681973 121029444187369192282685)
                  ·
                    rfl

theorem cell22_1060668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 3, 5].length) (baseStart_1060668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1060668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1060668 prefixEnd_1060668 := by exact prefixLift 1060668
  have htrace : WordTrace (prefixWord ++ tailWord_1060668) baseStart_1060668 baseEnd_1060668 := by
    simpa [prefixWord, tailWord_1060668, baseEnd_1060668] using wordTrace_append hprefix tailTrace_1060668
  have hstable : (prefixWord ++ tailWord_1060668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060668).length < 2 ^ (prefixWord ++ tailWord_1060668).sum := by decide
  have hdescent : baseEnd_1060668 < baseStart_1060668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060764 : List Nat := [2, 2, 3, 3, 1, 2, 3, 2, 4]
def baseStart_1060764 : Nat := 118140960795 + 1060764 * 2 ^ 59
def prefixEnd_1060764 : Nat := 4983230072969 + 3 ^ 40 * 1060764 * 2
def baseEnd_1060764 : Nat := 121040398441331775482587

theorem tailTrace_1060764 : CollatzResearch.WordTrace tailWord_1060764 prefixEnd_1060764 121040398441331775482587 := by
  unfold tailWord_1060764
  simp only [CollatzResearch.WordTrace]
  refine ⟨19344620764520333456550673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25792827686027111275400897 19344620764520333456550673)
  ·
    refine ⟨14508465573390250092413005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19344620764520333456550673 14508465573390250092413005)
    ·
      refine ⟨5440674590021343784654877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14508465573390250092413005 5440674590021343784654877)
      ·
        refine ⟨2040252971258003919245579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5440674590021343784654877 2040252971258003919245579)
        ·
          refine ⟨3060379456887005878868369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2040252971258003919245579 3060379456887005878868369)
          ·
            refine ⟨2295284592665254409151277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3060379456887005878868369 2295284592665254409151277)
            ·
              refine ⟨860731722249470403431729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2295284592665254409151277 860731722249470403431729)
              ·
                refine ⟨645548791687102802573797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 860731722249470403431729 645548791687102802573797)
                ·
                  refine ⟨121040398441331775482587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 645548791687102802573797 121040398441331775482587)
                  ·
                    rfl

theorem cell22_1060764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 2, 4].length) (baseStart_1060764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1060764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1060764 prefixEnd_1060764 := by exact prefixLift 1060764
  have htrace : WordTrace (prefixWord ++ tailWord_1060764) baseStart_1060764 baseEnd_1060764 := by
    simpa [prefixWord, tailWord_1060764, baseEnd_1060764] using wordTrace_append hprefix tailTrace_1060764
  have hstable : (prefixWord ++ tailWord_1060764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060764).length < 2 ^ (prefixWord ++ tailWord_1060764).sum := by decide
  have hdescent : baseEnd_1060764 < baseStart_1060764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060775 : List Nat := [1, 1, 6, 1, 2, 2, 2, 7]
def baseStart_1060775 : Nat := 118140960795 + 1060775 * 2 ^ 59
def prefixEnd_1060775 : Nat := 4983230072969 + 3 ^ 40 * 1060775 * 2
def baseEnd_1060775 : Nat := 40347217872088329380303

theorem tailTrace_1060775 : CollatzResearch.WordTrace tailWord_1060775 prefixEnd_1060775 40347217872088329380303 := by
  unfold tailWord_1060775
  simp only [CollatzResearch.WordTrace]
  refine ⟨38689642732000815791751779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25793095154667210527834519 38689642732000815791751779)
  ·
    refine ⟨58034464098001223687627669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38689642732000815791751779 58034464098001223687627669)
    ·
      refine ⟨2720365504593807360357547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 58034464098001223687627669 2720365504593807360357547)
      ·
        refine ⟨4080548256890711040536321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2720365504593807360357547 4080548256890711040536321)
        ·
          refine ⟨3060411192668033280402241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4080548256890711040536321 3060411192668033280402241)
          ·
            refine ⟨2295308394501024960301681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3060411192668033280402241 2295308394501024960301681)
            ·
              refine ⟨1721481295875768720226261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2295308394501024960301681 1721481295875768720226261)
              ·
                refine ⟨40347217872088329380303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1721481295875768720226261 40347217872088329380303)
                ·
                  rfl

theorem cell22_1060775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 7].length) (baseStart_1060775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1060775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1060775 prefixEnd_1060775 := by exact prefixLift 1060775
  have htrace : WordTrace (prefixWord ++ tailWord_1060775) baseStart_1060775 baseEnd_1060775 := by
    simpa [prefixWord, tailWord_1060775, baseEnd_1060775] using wordTrace_append hprefix tailTrace_1060775
  have hstable : (prefixWord ++ tailWord_1060775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060775).length < 2 ^ (prefixWord ++ tailWord_1060775).sum := by decide
  have hdescent : baseEnd_1060775 < baseStart_1060775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060807 : List Nat := [1, 1, 4, 1, 1, 2, 1, 7, 1, 3]
def baseStart_1060807 : Nat := 118140960795 + 1060807 * 2 ^ 59
def prefixEnd_1060807 : Nat := 4983230072969 + 3 ^ 40 * 1060807 * 2
def baseEnd_1060807 : Nat := 363135915102757547622629

theorem tailTrace_1060807 : CollatzResearch.WordTrace tailWord_1060807 prefixEnd_1060807 363135915102757547622629 := by
  unfold tailWord_1060807
  simp only [CollatzResearch.WordTrace]
  refine ⟨38690809867884885256916675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25793873245256590171277783 38690809867884885256916675)
  ·
    refine ⟨58036214801827327885375013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38690809867884885256916675 58036214801827327885375013)
    ·
      refine ⟨10881790275342623978507815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58036214801827327885375013 10881790275342623978507815)
      ·
        refine ⟨16322685413013935967761723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10881790275342623978507815 16322685413013935967761723)
        ·
          refine ⟨24484028119520903951642585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16322685413013935967761723 24484028119520903951642585)
          ·
            refine ⟨18363021089640677963731939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24484028119520903951642585 18363021089640677963731939)
            ·
              refine ⟨27544531634461016945597909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18363021089640677963731939 27544531634461016945597909)
              ·
                refine ⟨645574960182680084662451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 27544531634461016945597909 645574960182680084662451)
                ·
                  refine ⟨968362440274020126993677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 645574960182680084662451 968362440274020126993677)
                  ·
                    refine ⟨363135915102757547622629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 968362440274020126993677 363135915102757547622629)
                    ·
                      rfl

theorem cell22_1060807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 7, 1, 3].length) (baseStart_1060807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1060807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1060807 prefixEnd_1060807 := by exact prefixLift 1060807
  have htrace : WordTrace (prefixWord ++ tailWord_1060807) baseStart_1060807 baseEnd_1060807 := by
    simpa [prefixWord, tailWord_1060807, baseEnd_1060807] using wordTrace_append hprefix tailTrace_1060807
  have hstable : (prefixWord ++ tailWord_1060807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060807).length < 2 ^ (prefixWord ++ tailWord_1060807).sum := by decide
  have hdescent : baseEnd_1060807 < baseStart_1060807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060835 : List Nat := [1, 1, 1, 6, 1, 3, 1, 1, 2, 5]
def baseStart_1060835 : Nat := 118140960795 + 1060835 * 2 ^ 59
def prefixEnd_1060835 : Nat := 4983230072969 + 3 ^ 40 * 1060835 * 2
def baseEnd_1060835 : Nat := 363145500074974807922543

theorem tailTrace_1060835 : CollatzResearch.WordTrace tailWord_1060835 prefixEnd_1060835 363145500074974807922543 := by
  unfold tailWord_1060835
  simp only [CollatzResearch.WordTrace]
  refine ⟨38691831111783446038935959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25794554074522297359290639 38691831111783446038935959)
  ·
    refine ⟨58037746667675169058403939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38691831111783446038935959 58037746667675169058403939)
    ·
      refine ⟨87056620001512753587605909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58037746667675169058403939 87056620001512753587605909)
      ·
        refine ⟨4080779062570910324419027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 87056620001512753587605909 4080779062570910324419027)
        ·
          refine ⟨6121168593856365486628541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4080779062570910324419027 6121168593856365486628541)
          ·
            refine ⟨2295438222696137057485703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6121168593856365486628541 2295438222696137057485703)
            ·
              refine ⟨3443157334044205586228555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2295438222696137057485703 3443157334044205586228555)
              ·
                refine ⟨5164736001066308379342833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3443157334044205586228555 5164736001066308379342833)
                ·
                  refine ⟨3873552000799731284507125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5164736001066308379342833 3873552000799731284507125)
                  ·
                    refine ⟨363145500074974807922543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3873552000799731284507125 363145500074974807922543)
                    ·
                      rfl

theorem cell22_1060835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 5].length) (baseStart_1060835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1060835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1060835 prefixEnd_1060835 := by exact prefixLift 1060835
  have htrace : WordTrace (prefixWord ++ tailWord_1060835) baseStart_1060835 baseEnd_1060835 := by
    simpa [prefixWord, tailWord_1060835, baseEnd_1060835] using wordTrace_append hprefix tailTrace_1060835
  have hstable : (prefixWord ++ tailWord_1060835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060835).length < 2 ^ (prefixWord ++ tailWord_1060835).sum := by decide
  have hdescent : baseEnd_1060835 < baseStart_1060835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060848 : List Nat := [2, 1, 1, 1, 3, 2, 3, 1, 8]
def baseStart_1060848 : Nat := 118140960795 + 1060848 * 2 ^ 59
def prefixEnd_1060848 : Nat := 4983230072969 + 3 ^ 40 * 1060848 * 2
def baseEnd_1060848 : Nat := 121049983413549035782501

theorem tailTrace_1060848 : CollatzResearch.WordTrace tailWord_1060848 prefixEnd_1060848 121049983413549035782501 := by
  unfold tailWord_1060848
  simp only [CollatzResearch.WordTrace]
  refine ⟨19346152630368174629579599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25794870173824232839439465 19346152630368174629579599)
  ·
    refine ⟨29019228945552261944369399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19346152630368174629579599 29019228945552261944369399)
    ·
      refine ⟨43528843418328392916554099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29019228945552261944369399 43528843418328392916554099)
      ·
        refine ⟨65293265127492589374831149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43528843418328392916554099 65293265127492589374831149)
        ·
          refine ⟨24484974422809721015561681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65293265127492589374831149 24484974422809721015561681)
          ·
            refine ⟨18363730817107290761671261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24484974422809721015561681 18363730817107290761671261)
            ·
              refine ⟨6886399056415234035626723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18363730817107290761671261 6886399056415234035626723)
              ·
                refine ⟨10329598584622851053440085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6886399056415234035626723 10329598584622851053440085)
                ·
                  refine ⟨121049983413549035782501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10329598584622851053440085 121049983413549035782501)
                  ·
                    rfl

theorem cell22_1060848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 8].length) (baseStart_1060848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1060848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1060848 prefixEnd_1060848 := by exact prefixLift 1060848
  have htrace : WordTrace (prefixWord ++ tailWord_1060848) baseStart_1060848 baseEnd_1060848 := by
    simpa [prefixWord, tailWord_1060848, baseEnd_1060848] using wordTrace_append hprefix tailTrace_1060848
  have hstable : (prefixWord ++ tailWord_1060848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060848).length < 2 ^ (prefixWord ++ tailWord_1060848).sum := by decide
  have hdescent : baseEnd_1060848 < baseStart_1060848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060880 : List Nat := [2, 1, 1, 1, 1, 1, 1, 7, 4, 3]
def baseStart_1060880 : Nat := 118140960795 + 1060880 * 2 ^ 59
def prefixEnd_1060880 : Nat := 4983230072969 + 3 ^ 40 * 1060880 * 2
def baseEnd_1060880 : Nat := 363160904494609690547405

theorem tailTrace_1060880 : CollatzResearch.WordTrace tailWord_1060880 prefixEnd_1060880 363160904494609690547405 := by
  unfold tailWord_1060880
  simp only [CollatzResearch.WordTrace]
  refine ⟨19346736198310209362162047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25795648264413612482882729 19346736198310209362162047)
  ·
    refine ⟨29020104297465314043243071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19346736198310209362162047 29020104297465314043243071)
    ·
      refine ⟨43530156446197971064864607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29020104297465314043243071 43530156446197971064864607)
      ·
        refine ⟨65295234669296956597296911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43530156446197971064864607 65295234669296956597296911)
        ·
          refine ⟨97942852003945434895945367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65295234669296956597296911 97942852003945434895945367)
          ·
            refine ⟨146914278005918152343918051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97942852003945434895945367 146914278005918152343918051)
            ·
              refine ⟨220371417008877228515877077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146914278005918152343918051 220371417008877228515877077)
              ·
                refine ⟨5164955086145560043340869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 220371417008877228515877077 5164955086145560043340869)
                ·
                  refine ⟨968429078652292508126413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5164955086145560043340869 968429078652292508126413)
                  ·
                    refine ⟨363160904494609690547405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 968429078652292508126413 363160904494609690547405)
                    ·
                      rfl

theorem cell22_1060880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 4, 3].length) (baseStart_1060880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1060880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1060880 prefixEnd_1060880 := by exact prefixLift 1060880
  have htrace : WordTrace (prefixWord ++ tailWord_1060880) baseStart_1060880 baseEnd_1060880 := by
    simpa [prefixWord, tailWord_1060880, baseEnd_1060880] using wordTrace_append hprefix tailTrace_1060880
  have hstable : (prefixWord ++ tailWord_1060880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060880).length < 2 ^ (prefixWord ++ tailWord_1060880).sum := by decide
  have hdescent : baseEnd_1060880 < baseStart_1060880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061002 : List Nat := [3, 1, 2, 3, 1, 2, 1, 2, 3, 4]
def baseStart_1061002 : Nat := 118140960795 + 1061002 * 2 ^ 59
def prefixEnd_1061002 : Nat := 4983230072969 + 3 ^ 40 * 1061002 * 2
def baseEnd_1061002 : Nat := 363202667587842038997031

theorem tailTrace_1061002 : CollatzResearch.WordTrace tailWord_1061002 prefixEnd_1061002 363202667587842038997031 := by
  unfold tailWord_1061002
  simp only [CollatzResearch.WordTrace]
  refine ⟨9674480525544608390066315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25798614734785622373510173 9674480525544608390066315)
  ·
    refine ⟨14511720788316912585099473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9674480525544608390066315 14511720788316912585099473)
    ·
      refine ⟨10883790591237684438824605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14511720788316912585099473 10883790591237684438824605)
      ·
        refine ⟨4081421471714131664559227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10883790591237684438824605 4081421471714131664559227)
        ·
          refine ⟨6122132207571197496838841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4081421471714131664559227 6122132207571197496838841)
          ·
            refine ⟨4591599155678398122629131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6122132207571197496838841 4591599155678398122629131)
            ·
              refine ⟨6887398733517597183943697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4591599155678398122629131 6887398733517597183943697)
              ·
                refine ⟨5165549050138197887957773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6887398733517597183943697 5165549050138197887957773)
                ·
                  refine ⟨1937080893801824207984165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5165549050138197887957773 1937080893801824207984165)
                  ·
                    refine ⟨363202667587842038997031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1937080893801824207984165 363202667587842038997031)
                    ·
                      rfl

theorem cell22_1061002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_1061002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1061002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1061002 prefixEnd_1061002 := by exact prefixLift 1061002
  have htrace : WordTrace (prefixWord ++ tailWord_1061002) baseStart_1061002 baseEnd_1061002 := by
    simpa [prefixWord, tailWord_1061002, baseEnd_1061002] using wordTrace_append hprefix tailTrace_1061002
  have hstable : (prefixWord ++ tailWord_1061002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061002).length < 2 ^ (prefixWord ++ tailWord_1061002).sum := by decide
  have hdescent : baseEnd_1061002 < baseStart_1061002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061066 : List Nat := [3, 1, 2, 1, 3, 1, 5, 1, 2, 3]
def baseStart_1061066 : Nat := 118140960795 + 1061066 * 2 ^ 59
def prefixEnd_1061066 : Nat := 4983230072969 + 3 ^ 40 * 1061066 * 2
def baseEnd_1061066 : Nat := 363224576095767205396835

theorem tailTrace_1061066 : CollatzResearch.WordTrace tailWord_1061066 prefixEnd_1061066 363224576095767205396835 := by
  unfold tailWord_1061066
  simp only [CollatzResearch.WordTrace]
  refine ⟨9675064093486643122648763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25800170915964381660396701 9675064093486643122648763)
  ·
    refine ⟨14512596140229964683973145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9675064093486643122648763 14512596140229964683973145)
    ·
      refine ⟨10884447105172473512979859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14512596140229964683973145 10884447105172473512979859)
      ·
        refine ⟨16326670657758710269469789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10884447105172473512979859 16326670657758710269469789)
        ·
          refine ⟨6122501496659516351051171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16326670657758710269469789 6122501496659516351051171)
          ·
            refine ⟨9183752244989274526576757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6122501496659516351051171 9183752244989274526576757)
            ·
              refine ⟨860976772967744486866571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9183752244989274526576757 860976772967744486866571)
              ·
                refine ⟨1291465159451616730299857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 860976772967744486866571 1291465159451616730299857)
                ·
                  refine ⟨968598869588712547724893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1291465159451616730299857 968598869588712547724893)
                  ·
                    refine ⟨363224576095767205396835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 968598869588712547724893 363224576095767205396835)
                    ·
                      rfl

theorem cell22_1061066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 1, 2, 3].length) (baseStart_1061066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1061066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1061066 prefixEnd_1061066 := by exact prefixLift 1061066
  have htrace : WordTrace (prefixWord ++ tailWord_1061066) baseStart_1061066 baseEnd_1061066 := by
    simpa [prefixWord, tailWord_1061066, baseEnd_1061066] using wordTrace_append hprefix tailTrace_1061066
  have hstable : (prefixWord ++ tailWord_1061066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061066).length < 2 ^ (prefixWord ++ tailWord_1061066).sum := by decide
  have hdescent : baseEnd_1061066 < baseStart_1061066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061107 : List Nat := [1, 1, 1, 2, 2, 4, 2, 4, 5]
def baseStart_1061107 : Nat := 118140960795 + 1061107 * 2 ^ 59
def prefixEnd_1061107 : Nat := 4983230072969 + 3 ^ 40 * 1061107 * 2
def baseEnd_1061107 : Nat := 121079537077885588373903

theorem tailTrace_1061107 : CollatzResearch.WordTrace tailWord_1061107 prefixEnd_1061107 121079537077885588373903 := by
  unfold tailWord_1061107
  simp only [CollatzResearch.WordTrace]
  refine ⟨38701751766798036492837575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25801167844532024328558383 38701751766798036492837575)
  ·
    refine ⟨58052627650197054739256363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38701751766798036492837575 58052627650197054739256363)
    ·
      refine ⟨87078941475295582108884545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58052627650197054739256363 87078941475295582108884545)
      ·
        refine ⟨65309206106471686581663409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87078941475295582108884545 65309206106471686581663409)
        ·
          refine ⟨48981904579853764936247557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65309206106471686581663409 48981904579853764936247557)
          ·
            refine ⟨9184107108722580925546417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48981904579853764936247557 9184107108722580925546417)
            ·
              refine ⟨6888080331541935694159813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9184107108722580925546417 6888080331541935694159813)
              ·
                refine ⟨1291515062164112942654965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6888080331541935694159813 1291515062164112942654965)
                ·
                  refine ⟨121079537077885588373903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1291515062164112942654965 121079537077885588373903)
                  ·
                    rfl

theorem cell22_1061107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 4, 5].length) (baseStart_1061107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1061107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1061107 prefixEnd_1061107 := by exact prefixLift 1061107
  have htrace : WordTrace (prefixWord ++ tailWord_1061107) baseStart_1061107 baseEnd_1061107 := by
    simpa [prefixWord, tailWord_1061107, baseEnd_1061107] using wordTrace_append hprefix tailTrace_1061107
  have hstable : (prefixWord ++ tailWord_1061107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061107).length < 2 ^ (prefixWord ++ tailWord_1061107).sum := by decide
  have hdescent : baseEnd_1061107 < baseStart_1061107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061162 : List Nat := [3, 1, 4, 2, 2, 2, 2, 2, 1, 3]
def baseStart_1061162 : Nat := 118140960795 + 1061162 * 2 ^ 59
def prefixEnd_1061162 : Nat := 4983230072969 + 3 ^ 40 * 1061162 * 2
def baseEnd_1061162 : Nat := 363257438857654954996541

theorem tailTrace_1061162 : CollatzResearch.WordTrace tailWord_1061162 prefixEnd_1061162 363257438857654954996541 := by
  unfold tailWord_1061162
  simp only [CollatzResearch.WordTrace]
  refine ⟨9675939445399695221522435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25802505187732520590726493 9675939445399695221522435)
  ·
    refine ⟨14513909168099542832283653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9675939445399695221522435 14513909168099542832283653)
    ·
      refine ⟨2721357969018664281053185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14513909168099542832283653 2721357969018664281053185)
      ·
        refine ⟨2041018476763998210789889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2721357969018664281053185 2041018476763998210789889)
        ·
          refine ⟨1530763857572998658092417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2041018476763998210789889 1530763857572998658092417)
          ·
            refine ⟨1148072893179748993569313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1530763857572998658092417 1148072893179748993569313)
            ·
              refine ⟨861054669884811745176985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1148072893179748993569313 861054669884811745176985)
              ·
                refine ⟨645791002413608808882739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 861054669884811745176985 645791002413608808882739)
                ·
                  refine ⟨968686503620413213324109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 645791002413608808882739 968686503620413213324109)
                  ·
                    refine ⟨363257438857654954996541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 968686503620413213324109 363257438857654954996541)
                    ·
                      rfl

theorem cell22_1061162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_1061162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1061162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1061162 prefixEnd_1061162 := by exact prefixLift 1061162
  have htrace : WordTrace (prefixWord ++ tailWord_1061162) baseStart_1061162 baseEnd_1061162 := by
    simpa [prefixWord, tailWord_1061162, baseEnd_1061162] using wordTrace_append hprefix tailTrace_1061162
  have hstable : (prefixWord ++ tailWord_1061162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061162).length < 2 ^ (prefixWord ++ tailWord_1061162).sum := by decide
  have hdescent : baseEnd_1061162 < baseStart_1061162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061205 : List Nat := [1, 3, 2, 2, 5, 1, 2, 1, 1, 4]
def baseStart_1061205 : Nat := 118140960795 + 1061205 * 2 ^ 59
def prefixEnd_1061205 : Nat := 4983230072969 + 3 ^ 40 * 1061205 * 2
def baseEnd_1061205 : Nat := 363272158636417176171409

theorem tailTrace_1061205 : CollatzResearch.WordTrace tailWord_1061205 prefixEnd_1061205 363272158636417176171409 := by
  unfold tailWord_1061205
  simp only [CollatzResearch.WordTrace]
  refine ⟨38705326120442999229905069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25803550746961999486603379 38705326120442999229905069)
  ·
    refine ⟨14514497295166124711214401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38705326120442999229905069 14514497295166124711214401)
    ·
      refine ⟨10885872971374593533410801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14514497295166124711214401 10885872971374593533410801)
      ·
        refine ⟨8164404728530945150058101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10885872971374593533410801 8164404728530945150058101)
        ·
          refine ⟨765412943299776107817947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8164404728530945150058101 765412943299776107817947)
          ·
            refine ⟨1148119414949664161726921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 765412943299776107817947 1148119414949664161726921)
            ·
              refine ⟨861089561212248121295191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1148119414949664161726921 861089561212248121295191)
              ·
                refine ⟨1291634341818372181942787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 861089561212248121295191 1291634341818372181942787)
                ·
                  refine ⟨1937451512727558272914181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1291634341818372181942787 1937451512727558272914181)
                  ·
                    refine ⟨363272158636417176171409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1937451512727558272914181 363272158636417176171409)
                    ·
                      rfl

theorem cell22_1061205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 1, 1, 4].length) (baseStart_1061205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1061205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1061205 prefixEnd_1061205 := by exact prefixLift 1061205
  have htrace : WordTrace (prefixWord ++ tailWord_1061205) baseStart_1061205 baseEnd_1061205 := by
    simpa [prefixWord, tailWord_1061205, baseEnd_1061205] using wordTrace_append hprefix tailTrace_1061205
  have hstable : (prefixWord ++ tailWord_1061205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061205).length < 2 ^ (prefixWord ++ tailWord_1061205).sum := by decide
  have hdescent : baseEnd_1061205 < baseStart_1061205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061218 : List Nat := [3, 3, 2, 1, 1, 2, 3, 2, 2, 3]
def baseStart_1061218 : Nat := 118140960795 + 1061218 * 2 ^ 59
def prefixEnd_1061218 : Nat := 4983230072969 + 3 ^ 40 * 1061218 * 2
def baseEnd_1061218 : Nat := 363276608802089475596369

theorem tailTrace_1061218 : CollatzResearch.WordTrace tailWord_1061218 prefixEnd_1061218 363276608802089475596369 := by
  unfold tailWord_1061218
  simp only [CollatzResearch.WordTrace]
  refine ⟨9676450067348975612532077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25803866846263934966752205 9676450067348975612532077)
  ·
    refine ⟨3628668775255865854699529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9676450067348975612532077 3628668775255865854699529)
    ·
      refine ⟨2721501581441899391024647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3628668775255865854699529 2721501581441899391024647)
      ·
        refine ⟨4082252372162849086536971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2721501581441899391024647 4082252372162849086536971)
        ·
          refine ⟨6123378558244273629805457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4082252372162849086536971 6123378558244273629805457)
          ·
            refine ⟨4592533918683205222354093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6123378558244273629805457 4592533918683205222354093)
            ·
              refine ⟨1722200219506201958382785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4592533918683205222354093 1722200219506201958382785)
              ·
                refine ⟨1291650164629651468787089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1722200219506201958382785 1291650164629651468787089)
                ·
                  refine ⟨968737623472238601590317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1291650164629651468787089 968737623472238601590317)
                  ·
                    refine ⟨363276608802089475596369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 968737623472238601590317 363276608802089475596369)
                    ·
                      rfl

theorem cell22_1061218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_1061218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1061218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1061218 prefixEnd_1061218 := by exact prefixLift 1061218
  have htrace : WordTrace (prefixWord ++ tailWord_1061218) baseStart_1061218 baseEnd_1061218 := by
    simpa [prefixWord, tailWord_1061218, baseEnd_1061218] using wordTrace_append hprefix tailTrace_1061218
  have hstable : (prefixWord ++ tailWord_1061218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061218).length < 2 ^ (prefixWord ++ tailWord_1061218).sum := by decide
  have hdescent : baseEnd_1061218 < baseStart_1061218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061242 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 11]
def baseStart_1061242 : Nat := 118140960795 + 1061242 * 2 ^ 59
def prefixEnd_1061242 : Nat := 4983230072969 + 3 ^ 40 * 1061242 * 2
def baseEnd_1061242 : Nat := 121094941497520470998765

theorem tailTrace_1061242 : CollatzResearch.WordTrace tailWord_1061242 prefixEnd_1061242 121094941497520470998765 := by
  unfold tailWord_1061242
  simp only [CollatzResearch.WordTrace]
  refine ⟨9676668905327238637250495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25804450414205969699334653 9676668905327238637250495)
  ·
    refine ⟨14515003357990857955875743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9676668905327238637250495 14515003357990857955875743)
    ·
      refine ⟨21772505036986286933813615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14515003357990857955875743 21772505036986286933813615)
      ·
        refine ⟨32658757555479430400720423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21772505036986286933813615 32658757555479430400720423)
        ·
          refine ⟨48988136333219145601080635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32658757555479430400720423 48988136333219145601080635)
          ·
            refine ⟨73482204499828718401620953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48988136333219145601080635 73482204499828718401620953)
            ·
              refine ⟨55111653374871538801215715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73482204499828718401620953 55111653374871538801215715)
              ·
                refine ⟨82667480062307308201823573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55111653374871538801215715 82667480062307308201823573)
                ·
                  refine ⟨121094941497520470998765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 82667480062307308201823573 121094941497520470998765)
                  ·
                    rfl

theorem cell22_1061242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 11].length) (baseStart_1061242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1061242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1061242 prefixEnd_1061242 := by exact prefixLift 1061242
  have htrace : WordTrace (prefixWord ++ tailWord_1061242) baseStart_1061242 baseEnd_1061242 := by
    simpa [prefixWord, tailWord_1061242, baseEnd_1061242] using wordTrace_append hprefix tailTrace_1061242
  have hstable : (prefixWord ++ tailWord_1061242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061242).length < 2 ^ (prefixWord ++ tailWord_1061242).sum := by decide
  have hdescent : baseEnd_1061242 < baseStart_1061242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061280 : List Nat := [2, 1, 1, 4, 1, 4, 3, 2, 1, 3]
def baseStart_1061280 : Nat := 118140960795 + 1061280 * 2 ^ 59
def prefixEnd_1061280 : Nat := 4983230072969 + 3 ^ 40 * 1061280 * 2
def baseEnd_1061280 : Nat := 363297832669141980546179

theorem tailTrace_1061280 : CollatzResearch.WordTrace tailWord_1061280 prefixEnd_1061280 363297832669141980546179 := by
  unfold tailWord_1061280
  simp only [CollatzResearch.WordTrace]
  refine ⟨19354030797585643519442647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25805374396780858025923529 19354030797585643519442647)
  ·
    refine ⟨29031046196378465279163971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19354030797585643519442647 29031046196378465279163971)
    ·
      refine ⟨43546569294567697918745957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29031046196378465279163971 43546569294567697918745957)
      ·
        refine ⟨8164981742731443359764867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43546569294567697918745957 8164981742731443359764867)
        ·
          refine ⟨12247472614097165039647301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8164981742731443359764867 12247472614097165039647301)
          ·
            refine ⟨2296401115143218444933869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12247472614097165039647301 2296401115143218444933869)
            ·
              refine ⟨861150418178706916850201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2296401115143218444933869 861150418178706916850201)
              ·
                refine ⟨645862813634030187637651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 861150418178706916850201 645862813634030187637651)
                ·
                  refine ⟨968794220451045281456477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 645862813634030187637651 968794220451045281456477)
                  ·
                    refine ⟨363297832669141980546179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 968794220451045281456477 363297832669141980546179)
                    ·
                      rfl

theorem cell22_1061280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 2, 1, 3].length) (baseStart_1061280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1061280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1061280 prefixEnd_1061280 := by exact prefixLift 1061280
  have htrace : WordTrace (prefixWord ++ tailWord_1061280) baseStart_1061280 baseEnd_1061280 := by
    simpa [prefixWord, tailWord_1061280, baseEnd_1061280] using wordTrace_append hprefix tailTrace_1061280
  have hstable : (prefixWord ++ tailWord_1061280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061280).length < 2 ^ (prefixWord ++ tailWord_1061280).sum := by decide
  have hdescent : baseEnd_1061280 < baseStart_1061280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061293 : List Nat := [1, 5, 2, 2, 2, 1, 1, 3, 5]
def baseStart_1061293 : Nat := 118140960795 + 1061293 * 2 ^ 59
def prefixEnd_1061293 : Nat := 4983230072969 + 3 ^ 40 * 1061293 * 2
def baseEnd_1061293 : Nat := 121100760944938093323713

theorem tailTrace_1061293 : CollatzResearch.WordTrace tailWord_1061293 prefixEnd_1061293 121100760944938093323713 := by
  unfold tailWord_1061293
  simp only [CollatzResearch.WordTrace]
  refine ⟨38708535744124190259108533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25805690496082793506072355 38708535744124190259108533)
  ·
    refine ⟨3628925226011642836791425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38708535744124190259108533 3628925226011642836791425)
    ·
      refine ⟨2721693919508732127593569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3628925226011642836791425 2721693919508732127593569)
      ·
        refine ⟨2041270439631549095695177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2721693919508732127593569 2041270439631549095695177)
        ·
          refine ⟨1530952829723661821771383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2041270439631549095695177 1530952829723661821771383)
          ·
            refine ⟨2296429244585492732657075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1530952829723661821771383 2296429244585492732657075)
            ·
              refine ⟨3444643866878239098985613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2296429244585492732657075 3444643866878239098985613)
              ·
                refine ⟨1291741450079339662119605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3444643866878239098985613 1291741450079339662119605)
                ·
                  refine ⟨121100760944938093323713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1291741450079339662119605 121100760944938093323713)
                  ·
                    rfl

theorem cell22_1061293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_1061293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1061293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1061293 prefixEnd_1061293 := by exact prefixLift 1061293
  have htrace : WordTrace (prefixWord ++ tailWord_1061293) baseStart_1061293 baseEnd_1061293 := by
    simpa [prefixWord, tailWord_1061293, baseEnd_1061293] using wordTrace_append hprefix tailTrace_1061293
  have hstable : (prefixWord ++ tailWord_1061293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061293).length < 2 ^ (prefixWord ++ tailWord_1061293).sum := by decide
  have hdescent : baseEnd_1061293 < baseStart_1061293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061319 : List Nat := [1, 1, 4, 1, 1, 4, 1, 1, 3, 5]
def baseStart_1061319 : Nat := 118140960795 + 1061319 * 2 ^ 59
def prefixEnd_1061319 : Nat := 4983230072969 + 3 ^ 40 * 1061319 * 2
def baseEnd_1061319 : Nat := 363311183166158878821059

theorem tailTrace_1061319 : CollatzResearch.WordTrace tailWord_1061319 prefixEnd_1061319 363311183166158878821059 := by
  unfold tailWord_1061319
  simp only [CollatzResearch.WordTrace]
  refine ⟨38709484042029996699555011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25806322694686664466370007 38709484042029996699555011)
  ·
    refine ⟨58064226063044995049332517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38709484042029996699555011 58064226063044995049332517)
    ·
      refine ⟨10887042386820936571749847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58064226063044995049332517 10887042386820936571749847)
      ·
        refine ⟨16330563580231404857624771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10887042386820936571749847 16330563580231404857624771)
        ·
          refine ⟨24495845370347107286437157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16330563580231404857624771 24495845370347107286437157)
          ·
            refine ⟨4592971006940082616206967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24495845370347107286437157 4592971006940082616206967)
            ·
              refine ⟨6889456510410123924310451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4592971006940082616206967 6889456510410123924310451)
              ·
                refine ⟨10334184765615185886465677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6889456510410123924310451 10334184765615185886465677)
                ·
                  refine ⟨3875319287105694707424629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10334184765615185886465677 3875319287105694707424629)
                  ·
                    refine ⟨363311183166158878821059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3875319287105694707424629 363311183166158878821059)
                    ·
                      rfl

theorem cell22_1061319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_1061319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1061319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1061319 prefixEnd_1061319 := by exact prefixLift 1061319
  have htrace : WordTrace (prefixWord ++ tailWord_1061319) baseStart_1061319 baseEnd_1061319 := by
    simpa [prefixWord, tailWord_1061319, baseEnd_1061319] using wordTrace_append hprefix tailTrace_1061319
  have hstable : (prefixWord ++ tailWord_1061319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061319).length < 2 ^ (prefixWord ++ tailWord_1061319).sum := by decide
  have hdescent : baseEnd_1061319 < baseStart_1061319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061488 : List Nat := [2, 1, 1, 1, 7, 1, 1, 2, 1, 5]
def baseStart_1061488 : Nat := 118140960795 + 1061488 * 2 ^ 59
def prefixEnd_1061488 : Nat := 4983230072969 + 3 ^ 40 * 1061488 * 2
def baseEnd_1061488 : Nat := 363369035319898771345541

theorem tailTrace_1061488 : CollatzResearch.WordTrace tailWord_1061488 prefixEnd_1061488 363369035319898771345541 := by
  unfold tailWord_1061488
  simp only [CollatzResearch.WordTrace]
  refine ⟨19357823989208869281228559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25810431985611825708304745 19357823989208869281228559)
  ·
    refine ⟨29036735983813303921842839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19357823989208869281228559 29036735983813303921842839)
    ·
      refine ⟨43555103975719955882764259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29036735983813303921842839 43555103975719955882764259)
      ·
        refine ⟨65332655963579933824146389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43555103975719955882764259 65332655963579933824146389)
        ·
          refine ⟨1531234124146404699003431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 65332655963579933824146389 1531234124146404699003431)
          ·
            refine ⟨2296851186219607048505147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1531234124146404699003431 2296851186219607048505147)
            ·
              refine ⟨3445276779329410572757721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2296851186219607048505147 3445276779329410572757721)
              ·
                refine ⟨2583957584497057929568291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3445276779329410572757721 2583957584497057929568291)
                ·
                  refine ⟨3875936376745586894352437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2583957584497057929568291 3875936376745586894352437)
                  ·
                    refine ⟨363369035319898771345541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3875936376745586894352437 363369035319898771345541)
                    ·
                      rfl

theorem cell22_1061488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 1, 5].length) (baseStart_1061488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1061488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1061488 prefixEnd_1061488 := by exact prefixLift 1061488
  have htrace : WordTrace (prefixWord ++ tailWord_1061488) baseStart_1061488 baseEnd_1061488 := by
    simpa [prefixWord, tailWord_1061488, baseEnd_1061488] using wordTrace_append hprefix tailTrace_1061488
  have hstable : (prefixWord ++ tailWord_1061488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061488).length < 2 ^ (prefixWord ++ tailWord_1061488).sum := by decide
  have hdescent : baseEnd_1061488 < baseStart_1061488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061501 : List Nat := [1, 4, 1, 1, 5, 10]
def baseStart_1061501 : Nat := 118140960795 + 1061501 * 2 ^ 59
def prefixEnd_1061501 : Nat := 4983230072969 + 3 ^ 40 * 1061501 * 2
def baseEnd_1061501 : Nat := 4486092413402111984821

theorem tailTrace_1061501 : CollatzResearch.WordTrace tailWord_1061501 prefixEnd_1061501 4486092413402111984821 := by
  unfold tailWord_1061501
  simp only [CollatzResearch.WordTrace]
  refine ⟨38716122127370641782680357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25810748084913761188453571 38716122127370641782680357)
  ·
    refine ⟨7259272898881995334252567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38716122127370641782680357 7259272898881995334252567)
    ·
      refine ⟨10888909348322993001378851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7259272898881995334252567 10888909348322993001378851)
      ·
        refine ⟨16333364022484489502068277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10888909348322993001378851 16333364022484489502068277)
        ·
          refine ⟨1531252877107920890818901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16333364022484489502068277 1531252877107920890818901)
          ·
            refine ⟨4486092413402111984821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1531252877107920890818901 4486092413402111984821)
            ·
              rfl

theorem cell22_1061501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 10].length) (baseStart_1061501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1061501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1061501 prefixEnd_1061501 := by exact prefixLift 1061501
  have htrace : WordTrace (prefixWord ++ tailWord_1061501) baseStart_1061501 baseEnd_1061501 := by
    simpa [prefixWord, tailWord_1061501, baseEnd_1061501] using wordTrace_append hprefix tailTrace_1061501
  have hstable : (prefixWord ++ tailWord_1061501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061501).length < 2 ^ (prefixWord ++ tailWord_1061501).sum := by decide
  have hdescent : baseEnd_1061501 < baseStart_1061501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061505 : List Nat := [1, 2, 4, 2, 1, 1, 4, 2, 2, 3]
def baseStart_1061505 : Nat := 118140960795 + 1061505 * 2 ^ 59
def prefixEnd_1061505 : Nat := 4983230072969 + 3 ^ 40 * 1061505 * 2
def baseEnd_1061505 : Nat := 363374854767316393670489

theorem tailTrace_1061505 : CollatzResearch.WordTrace tailWord_1061505 prefixEnd_1061505 363374854767316393670489 := by
  unfold tailWord_1061505
  simp only [CollatzResearch.WordTrace]
  refine ⟨38716268019356150465825969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25810845346237433643883979 38716268019356150465825969)
  ·
    refine ⟨29037201014517112849369477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38716268019356150465825969 29037201014517112849369477)
    ·
      refine ⟨5444475190221958659256777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29037201014517112849369477 5444475190221958659256777)
      ·
        refine ⟨4083356392666468994442583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5444475190221958659256777 4083356392666468994442583)
        ·
          refine ⟨6125034588999703491663875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4083356392666468994442583 6125034588999703491663875)
          ·
            refine ⟨9187551883499555237495813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6125034588999703491663875 9187551883499555237495813)
            ·
              refine ⟨1722665978156166607030465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9187551883499555237495813 1722665978156166607030465)
              ·
                refine ⟨1291999483617124955272849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1722665978156166607030465 1291999483617124955272849)
                ·
                  refine ⟨968999612712843716454637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1291999483617124955272849 968999612712843716454637)
                  ·
                    refine ⟨363374854767316393670489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 968999612712843716454637 363374854767316393670489)
                    ·
                      rfl

theorem cell22_1061505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_1061505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1061505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1061505 prefixEnd_1061505 := by exact prefixLift 1061505
  have htrace : WordTrace (prefixWord ++ tailWord_1061505) baseStart_1061505 baseEnd_1061505 := by
    simpa [prefixWord, tailWord_1061505, baseEnd_1061505] using wordTrace_append hprefix tailTrace_1061505
  have hstable : (prefixWord ++ tailWord_1061505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061505).length < 2 ^ (prefixWord ++ tailWord_1061505).sum := by decide
  have hdescent : baseEnd_1061505 < baseStart_1061505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061533 : List Nat := [1, 4, 2, 1, 1, 1, 3, 1, 5, 3]
def baseStart_1061533 : Nat := 118140960795 + 1061533 * 2 ^ 59
def prefixEnd_1061533 : Nat := 4983230072969 + 3 ^ 40 * 1061533 * 2
def baseEnd_1061533 : Nat := 363384439739533653970403

theorem tailTrace_1061533 : CollatzResearch.WordTrace tailWord_1061533 prefixEnd_1061533 363384439739533653970403 := by
  unfold tailWord_1061533
  simp only [CollatzResearch.WordTrace]
  refine ⟨38717289263254711247845253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25811526175503140831896835 38717289263254711247845253)
  ·
    refine ⟨7259491736860258358970985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38717289263254711247845253 7259491736860258358970985)
    ·
      refine ⟨5444618802645193769228239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7259491736860258358970985 5444618802645193769228239)
      ·
        refine ⟨8166928203967790653842359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5444618802645193769228239 8166928203967790653842359)
        ·
          refine ⟨12250392305951685980763539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8166928203967790653842359 12250392305951685980763539)
          ·
            refine ⟨18375588458927528971145309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12250392305951685980763539 18375588458927528971145309)
            ·
              refine ⟨6890845672097823364179491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18375588458927528971145309 6890845672097823364179491)
              ·
                refine ⟨10336268508146735046269237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6890845672097823364179491 10336268508146735046269237)
                ·
                  refine ⟨969025172638756410587741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10336268508146735046269237 969025172638756410587741)
                  ·
                    refine ⟨363384439739533653970403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 969025172638756410587741 363384439739533653970403)
                    ·
                      rfl

theorem cell22_1061533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_1061533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1061533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1061533 prefixEnd_1061533 := by exact prefixLift 1061533
  have htrace : WordTrace (prefixWord ++ tailWord_1061533) baseStart_1061533 baseEnd_1061533 := by
    simpa [prefixWord, tailWord_1061533, baseEnd_1061533] using wordTrace_append hprefix tailTrace_1061533
  have hstable : (prefixWord ++ tailWord_1061533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061533).length < 2 ^ (prefixWord ++ tailWord_1061533).sum := by decide
  have hdescent : baseEnd_1061533 < baseStart_1061533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061537 : List Nat := [1, 2, 3, 3, 4, 1, 1, 1, 2, 4]
def baseStart_1061537 : Nat := 118140960795 + 1061537 * 2 ^ 59
def prefixEnd_1061537 : Nat := 4983230072969 + 3 ^ 40 * 1061537 * 2
def baseEnd_1061537 : Nat := 363385809021278976870391

theorem tailTrace_1061537 : CollatzResearch.WordTrace tailWord_1061537 prefixEnd_1061537 363385809021278976870391 := by
  unfold tailWord_1061537
  simp only [CollatzResearch.WordTrace]
  refine ⟨38717435155240219930990865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25811623436826813287327243 38717435155240219930990865)
  ·
    refine ⟨29038076366430164948243149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38717435155240219930990865 29038076366430164948243149)
    ·
      refine ⟨10889278637411311855591181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29038076366430164948243149 10889278637411311855591181)
      ·
        refine ⟨4083479489029241945846693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10889278637411311855591181 4083479489029241945846693)
        ·
          refine ⟨765652404192982864846255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4083479489029241945846693 765652404192982864846255)
          ·
            refine ⟨1148478606289474297269383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 765652404192982864846255 1148478606289474297269383)
            ·
              refine ⟨1722717909434211445904075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1148478606289474297269383 1722717909434211445904075)
              ·
                refine ⟨2584076864151317168856113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1722717909434211445904075 2584076864151317168856113)
                ·
                  refine ⟨1938057648113487876642085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2584076864151317168856113 1938057648113487876642085)
                  ·
                    refine ⟨363385809021278976870391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1938057648113487876642085 363385809021278976870391)
                    ·
                      rfl

theorem cell22_1061537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 2, 4].length) (baseStart_1061537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1061537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1061537 prefixEnd_1061537 := by exact prefixLift 1061537
  have htrace : WordTrace (prefixWord ++ tailWord_1061537) baseStart_1061537 baseEnd_1061537 := by
    simpa [prefixWord, tailWord_1061537, baseEnd_1061537] using wordTrace_append hprefix tailTrace_1061537
  have hstable : (prefixWord ++ tailWord_1061537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061537).length < 2 ^ (prefixWord ++ tailWord_1061537).sum := by decide
  have hdescent : baseEnd_1061537 < baseStart_1061537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061578 : List Nat := [3, 1, 2, 1, 4, 1, 2, 1, 2, 5]
def baseStart_1061578 : Nat := 118140960795 + 1061578 * 2 ^ 59
def prefixEnd_1061578 : Nat := 4983230072969 + 3 ^ 40 * 1061578 * 2
def baseEnd_1061578 : Nat := 363399844159168536595265

theorem tailTrace_1061578 : CollatzResearch.WordTrace tailWord_1061578 prefixEnd_1061578 363399844159168536595265 := by
  unfold tailWord_1061578
  simp only [CollatzResearch.WordTrace]
  refine ⟨9679732637022920983308347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25812620365394455955488925 9679732637022920983308347)
  ·
    refine ⟨14519598955534381474962521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9679732637022920983308347 14519598955534381474962521)
    ·
      refine ⟨10889699216650786106221891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14519598955534381474962521 10889699216650786106221891)
      ·
        refine ⟨16334548824976179159332837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10889699216650786106221891 16334548824976179159332837)
        ·
          refine ⟨3062727904683033592374907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16334548824976179159332837 3062727904683033592374907)
          ·
            refine ⟨4594091857024550388562361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3062727904683033592374907 4594091857024550388562361)
            ·
              refine ⟨3445568892768412791421771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4594091857024550388562361 3445568892768412791421771)
              ·
                refine ⟨5168353339152619187132657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3445568892768412791421771 5168353339152619187132657)
                ·
                  refine ⟨3876265004364464390349493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5168353339152619187132657 3876265004364464390349493)
                  ·
                    refine ⟨363399844159168536595265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3876265004364464390349493 363399844159168536595265)
                    ·
                      rfl

theorem cell22_1061578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_1061578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1061578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1061578 prefixEnd_1061578 := by exact prefixLift 1061578
  have htrace : WordTrace (prefixWord ++ tailWord_1061578) baseStart_1061578 baseEnd_1061578 := by
    simpa [prefixWord, tailWord_1061578, baseEnd_1061578] using wordTrace_append hprefix tailTrace_1061578
  have hstable : (prefixWord ++ tailWord_1061578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061578).length < 2 ^ (prefixWord ++ tailWord_1061578).sum := by decide
  have hdescent : baseEnd_1061578 < baseStart_1061578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061683 : List Nat := [1, 1, 1, 2, 6, 1, 1, 1, 2, 6]
def baseStart_1061683 : Nat := 118140960795 + 1061683 * 2 ^ 59
def prefixEnd_1061683 : Nat := 4983230072969 + 3 ^ 40 * 1061683 * 2
def baseEnd_1061683 : Nat := 363435787804983262719943

theorem tailTrace_1061683 : CollatzResearch.WordTrace tailWord_1061683 prefixEnd_1061683 363435787804983262719943 := by
  unfold tailWord_1061683
  simp only [CollatzResearch.WordTrace]
  refine ⟨38722760212711286865805703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25815173475140857910537135 38722760212711286865805703)
  ·
    refine ⟨58084140319066930298708555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38722760212711286865805703 58084140319066930298708555)
    ·
      refine ⟨87126210478600395448062833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58084140319066930298708555 87126210478600395448062833)
      ·
        refine ⟨65344657858950296586047125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87126210478600395448062833 65344657858950296586047125)
        ·
          refine ⟨3063030837138295152470959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 65344657858950296586047125 3063030837138295152470959)
          ·
            refine ⟨4594546255707442728706439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3063030837138295152470959 4594546255707442728706439)
            ·
              refine ⟨6891819383561164093059659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4594546255707442728706439 6891819383561164093059659)
              ·
                refine ⟨10337729075341746139589489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6891819383561164093059659 10337729075341746139589489)
                ·
                  refine ⟨7753296806506309604692117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10337729075341746139589489 7753296806506309604692117)
                  ·
                    refine ⟨363435787804983262719943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7753296806506309604692117 363435787804983262719943)
                    ·
                      rfl

theorem cell22_1061683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 6].length) (baseStart_1061683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1061683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1061683 prefixEnd_1061683 := by exact prefixLift 1061683
  have htrace : WordTrace (prefixWord ++ tailWord_1061683) baseStart_1061683 baseEnd_1061683 := by
    simpa [prefixWord, tailWord_1061683, baseEnd_1061683] using wordTrace_append hprefix tailTrace_1061683
  have hstable : (prefixWord ++ tailWord_1061683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061683).length < 2 ^ (prefixWord ++ tailWord_1061683).sum := by decide
  have hdescent : baseEnd_1061683 < baseStart_1061683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061719 : List Nat := [1, 1, 3, 2, 4, 2, 2, 3, 1, 3]
def baseStart_1061719 : Nat := 118140960795 + 1061719 * 2 ^ 59
def prefixEnd_1061719 : Nat := 4983230072969 + 3 ^ 40 * 1061719 * 2
def baseEnd_1061719 : Nat := 363448111340691168819833

theorem tailTrace_1061719 : CollatzResearch.WordTrace tailWord_1061719 prefixEnd_1061719 363448111340691168819833 := by
  unfold tailWord_1061719
  simp only [CollatzResearch.WordTrace]
  refine ⟨38724073240580865014116211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25816048827053910009410807 38724073240580865014116211)
  ·
    refine ⟨58086109860871297521174317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38724073240580865014116211 58086109860871297521174317)
    ·
      refine ⟨21782291197826736570440369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58086109860871297521174317 21782291197826736570440369)
      ·
        refine ⟨16336718398370052427830277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21782291197826736570440369 16336718398370052427830277)
        ·
          refine ⟨3063134699694384830218177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16336718398370052427830277 3063134699694384830218177)
          ·
            refine ⟨2297351024770788622663633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3063134699694384830218177 2297351024770788622663633)
            ·
              refine ⟨1723013268578091466997725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2297351024770788622663633 1723013268578091466997725)
              ·
                refine ⟨646129975716784300124147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1723013268578091466997725 646129975716784300124147)
                ·
                  refine ⟨969194963575176450186221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 646129975716784300124147 969194963575176450186221)
                  ·
                    refine ⟨363448111340691168819833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 969194963575176450186221 363448111340691168819833)
                    ·
                      rfl

theorem cell22_1061719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 3, 1, 3].length) (baseStart_1061719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1061719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1061719 prefixEnd_1061719 := by exact prefixLift 1061719
  have htrace : WordTrace (prefixWord ++ tailWord_1061719) baseStart_1061719 baseEnd_1061719 := by
    simpa [prefixWord, tailWord_1061719, baseEnd_1061719] using wordTrace_append hprefix tailTrace_1061719
  have hstable : (prefixWord ++ tailWord_1061719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061719).length < 2 ^ (prefixWord ++ tailWord_1061719).sum := by decide
  have hdescent : baseEnd_1061719 < baseStart_1061719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061732 : List Nat := [2, 3, 1, 1, 4, 3, 1, 2, 5]
def baseStart_1061732 : Nat := 118140960795 + 1061732 * 2 ^ 59
def prefixEnd_1061732 : Nat := 4983230072969 + 3 ^ 40 * 1061732 * 2
def baseEnd_1061732 : Nat := 121150853835454489414931

theorem tailTrace_1061732 : CollatzResearch.WordTrace tailWord_1061732 prefixEnd_1061732 121150853835454489414931 := by
  unfold tailWord_1061732
  simp only [CollatzResearch.WordTrace]
  refine ⟨19362273694766884117169725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25816364926355845489559633 19362273694766884117169725)
  ·
    refine ⟨7260852635537581543938647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19362273694766884117169725 7260852635537581543938647)
    ·
      refine ⟨10891278953306372315907971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7260852635537581543938647 10891278953306372315907971)
      ·
        refine ⟨16336918429959558473861957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10891278953306372315907971 16336918429959558473861957)
        ·
          refine ⟨3063172205617417213849117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16336918429959558473861957 3063172205617417213849117)
          ·
            refine ⟨1148689577106531455193419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3063172205617417213849117 1148689577106531455193419)
            ·
              refine ⟨1723034365659797182790129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1148689577106531455193419 1723034365659797182790129)
              ·
                refine ⟨1292275774244847887092597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1723034365659797182790129 1292275774244847887092597)
                ·
                  refine ⟨121150853835454489414931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1292275774244847887092597 121150853835454489414931)
                  ·
                    rfl

theorem cell22_1061732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 2, 5].length) (baseStart_1061732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1061732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1061732 prefixEnd_1061732 := by exact prefixLift 1061732
  have htrace : WordTrace (prefixWord ++ tailWord_1061732) baseStart_1061732 baseEnd_1061732 := by
    simpa [prefixWord, tailWord_1061732, baseEnd_1061732] using wordTrace_append hprefix tailTrace_1061732
  have hstable : (prefixWord ++ tailWord_1061732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061732).length < 2 ^ (prefixWord ++ tailWord_1061732).sum := by decide
  have hdescent : baseEnd_1061732 < baseStart_1061732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061809 : List Nat := [1, 2, 2, 4, 3, 1, 1, 3, 2, 3]
def baseStart_1061809 : Nat := 118140960795 + 1061809 * 2 ^ 59
def prefixEnd_1061809 : Nat := 4983230072969 + 3 ^ 40 * 1061809 * 2
def baseEnd_1061809 : Nat := 363478920179960934069557

theorem tailTrace_1061809 : CollatzResearch.WordTrace tailWord_1061809 prefixEnd_1061809 363478920179960934069557 := by
  unfold tailWord_1061809
  simp only [CollatzResearch.WordTrace]
  refine ⟨38727355810254810384892481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25818237206836540256594987 38727355810254810384892481)
  ·
    refine ⟨29045516857691107788669361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38727355810254810384892481 29045516857691107788669361)
    ·
      refine ⟨21784137643268330841502021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29045516857691107788669361 21784137643268330841502021)
      ·
        refine ⟨4084525808112812032781629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21784137643268330841502021 4084525808112812032781629)
        ·
          refine ⟨1531697178042304512293111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4084525808112812032781629 1531697178042304512293111)
          ·
            refine ⟨2297545767063456768439667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1531697178042304512293111 2297545767063456768439667)
            ·
              refine ⟨3446318650595185152659501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2297545767063456768439667 3446318650595185152659501)
              ·
                refine ⟨1292369493973194432247313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3446318650595185152659501 1292369493973194432247313)
                ·
                  refine ⟨969277120479895824185485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1292369493973194432247313 969277120479895824185485)
                  ·
                    refine ⟨363478920179960934069557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 969277120479895824185485 363478920179960934069557)
                    ·
                      rfl

theorem cell22_1061809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 3, 2, 3].length) (baseStart_1061809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1061809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1061809 prefixEnd_1061809 := by exact prefixLift 1061809
  have htrace : WordTrace (prefixWord ++ tailWord_1061809) baseStart_1061809 baseEnd_1061809 := by
    simpa [prefixWord, tailWord_1061809, baseEnd_1061809] using wordTrace_append hprefix tailTrace_1061809
  have hstable : (prefixWord ++ tailWord_1061809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061809).length < 2 ^ (prefixWord ++ tailWord_1061809).sum := by decide
  have hdescent : baseEnd_1061809 < baseStart_1061809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061895 : List Nat := [1, 1, 4, 3, 1, 1, 1, 2, 8]
def baseStart_1061895 : Nat := 118140960795 + 1061895 * 2 ^ 59
def prefixEnd_1061895 : Nat := 4983230072969 + 3 ^ 40 * 1061895 * 2
def baseEnd_1061895 : Nat := 121169453245828458806431

theorem tailTrace_1061895 : CollatzResearch.WordTrace tailWord_1061895 prefixEnd_1061895 121169453245828458806431 := by
  unfold tailWord_1061895
  simp only [CollatzResearch.WordTrace]
  refine ⟨38730492487943247072523139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25820328325295498048348759 38730492487943247072523139)
  ·
    refine ⟨58095738731914870608784709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38730492487943247072523139 58095738731914870608784709)
    ·
      refine ⟨10892951012234038239147133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58095738731914870608784709 10892951012234038239147133)
      ·
        refine ⟨4084856629587764339680175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10892951012234038239147133 4084856629587764339680175)
        ·
          refine ⟨6127284944381646509520263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4084856629587764339680175 6127284944381646509520263)
          ·
            refine ⟨9190927416572469764280395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6127284944381646509520263 9190927416572469764280395)
            ·
              refine ⟨13786391124858704646420593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9190927416572469764280395 13786391124858704646420593)
              ·
                refine ⟨10339793343644028484815445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13786391124858704646420593 10339793343644028484815445)
                ·
                  refine ⟨121169453245828458806431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10339793343644028484815445 121169453245828458806431)
                  ·
                    rfl

theorem cell22_1061895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 8].length) (baseStart_1061895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1061895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1061895 prefixEnd_1061895 := by exact prefixLift 1061895
  have htrace : WordTrace (prefixWord ++ tailWord_1061895) baseStart_1061895 baseEnd_1061895 := by
    simpa [prefixWord, tailWord_1061895, baseEnd_1061895] using wordTrace_append hprefix tailTrace_1061895
  have hstable : (prefixWord ++ tailWord_1061895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061895).length < 2 ^ (prefixWord ++ tailWord_1061895).sum := by decide
  have hdescent : baseEnd_1061895 < baseStart_1061895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061912 : List Nat := [2, 1, 2, 3, 2, 3, 2, 1, 6]
def baseStart_1061912 : Nat := 118140960795 + 1061912 * 2 ^ 59
def prefixEnd_1061912 : Nat := 4983230072969 + 3 ^ 40 * 1061912 * 2
def baseEnd_1061912 : Nat := 121171393061634332914747

theorem tailTrace_1061912 : CollatzResearch.WordTrace tailWord_1061912 prefixEnd_1061912 121171393061634332914747 := by
  unfold tailWord_1061912
  simp only [CollatzResearch.WordTrace]
  refine ⟨19365556264440829487945995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25820741685921105983927993 19365556264440829487945995)
  ·
    refine ⟨29048334396661244231918993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19365556264440829487945995 29048334396661244231918993)
    ·
      refine ⟨21786250797495933173939245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29048334396661244231918993 21786250797495933173939245)
      ·
        refine ⟨8169844049060974940227217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21786250797495933173939245 8169844049060974940227217)
        ·
          refine ⟨6127383036795731205170413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8169844049060974940227217 6127383036795731205170413)
          ·
            refine ⟨2297768638798399201938905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6127383036795731205170413 2297768638798399201938905)
            ·
              refine ⟨1723326479098799401454179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2297768638798399201938905 1723326479098799401454179)
              ·
                refine ⟨2584989718648199102181269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1723326479098799401454179 2584989718648199102181269)
                ·
                  refine ⟨121171393061634332914747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2584989718648199102181269 121171393061634332914747)
                  ·
                    rfl

theorem cell22_1061912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 6].length) (baseStart_1061912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1061912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1061912 prefixEnd_1061912 := by exact prefixLift 1061912
  have htrace : WordTrace (prefixWord ++ tailWord_1061912) baseStart_1061912 baseEnd_1061912 := by
    simpa [prefixWord, tailWord_1061912, baseEnd_1061912] using wordTrace_append hprefix tailTrace_1061912
  have hstable : (prefixWord ++ tailWord_1061912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061912).length < 2 ^ (prefixWord ++ tailWord_1061912).sum := by decide
  have hdescent : baseEnd_1061912 < baseStart_1061912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061925 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 3, 6]
def baseStart_1061925 : Nat := 118140960795 + 1061925 * 2 ^ 59
def prefixEnd_1061925 : Nat := 4983230072969 + 3 ^ 40 * 1061925 * 2
def baseEnd_1061925 : Nat := 363518629350575298169201

theorem tailTrace_1061925 : CollatzResearch.WordTrace tailWord_1061925 prefixEnd_1061925 363518629350575298169201 := by
  unfold tailWord_1061925
  simp only [CollatzResearch.WordTrace]
  refine ⟨38731586677834562196115229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25821057785223041464076819 38731586677834562196115229)
  ·
    refine ⟨14524345004187960823543211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38731586677834562196115229 14524345004187960823543211)
    ·
      refine ⟨21786517506281941235314817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14524345004187960823543211 21786517506281941235314817)
      ·
        refine ⟨16339888129711455926486113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21786517506281941235314817 16339888129711455926486113)
        ·
          refine ⟨12254916097283591944864585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16339888129711455926486113 12254916097283591944864585)
          ·
            refine ⟨9191187072962693958648439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12254916097283591944864585 9191187072962693958648439)
            ·
              refine ⟨13786780609444040937972659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9191187072962693958648439 13786780609444040937972659)
              ·
                refine ⟨20680170914166061406958989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13786780609444040937972659 20680170914166061406958989)
                ·
                  refine ⟨7755064092812273027609621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20680170914166061406958989 7755064092812273027609621)
                  ·
                    refine ⟨363518629350575298169201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7755064092812273027609621 363518629350575298169201)
                    ·
                      rfl

theorem cell22_1061925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_1061925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1061925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1061925 prefixEnd_1061925 := by exact prefixLift 1061925
  have htrace : WordTrace (prefixWord ++ tailWord_1061925) baseStart_1061925 baseEnd_1061925 := by
    simpa [prefixWord, tailWord_1061925, baseEnd_1061925] using wordTrace_append hprefix tailTrace_1061925
  have hstable : (prefixWord ++ tailWord_1061925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061925).length < 2 ^ (prefixWord ++ tailWord_1061925).sum := by decide
  have hdescent : baseEnd_1061925 < baseStart_1061925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062014 : List Nat := [4, 2, 4, 1, 2, 1, 2, 2, 4]
def baseStart_1062014 : Nat := 118140960795 + 1062014 * 2 ^ 59
def prefixEnd_1062014 : Nat := 4983230072969 + 3 ^ 40 * 1062014 * 2
def baseEnd_1062014 : Nat := 121183031956469577564643

theorem tailTrace_1062014 : CollatzResearch.WordTrace tailWord_1062014 prefixEnd_1062014 121183031956469577564643 := by
  unfold tailWord_1062014
  simp only [CollatzResearch.WordTrace]
  refine ⟨4841854096814016299513137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25823221849674753597403397 4841854096814016299513137)
  ·
    refine ⟨3631390572610512224634853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4841854096814016299513137 3631390572610512224634853)
    ·
      refine ⟨680885732364471042119035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3631390572610512224634853 680885732364471042119035)
      ·
        refine ⟨1021328598546706563178553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 680885732364471042119035 1021328598546706563178553)
        ·
          refine ⟨765996448910029922383915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1021328598546706563178553 765996448910029922383915)
          ·
            refine ⟨1148994673365044883575873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 765996448910029922383915 1148994673365044883575873)
            ·
              refine ⟨861746005023783662681905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1148994673365044883575873 861746005023783662681905)
              ·
                refine ⟨646309503767837747011429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 861746005023783662681905 646309503767837747011429)
                ·
                  refine ⟨121183031956469577564643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 646309503767837747011429 121183031956469577564643)
                  ·
                    rfl

theorem cell22_1062014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_1062014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1062014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1062014 prefixEnd_1062014 := by exact prefixLift 1062014
  have htrace : WordTrace (prefixWord ++ tailWord_1062014) baseStart_1062014 baseEnd_1062014 := by
    simpa [prefixWord, tailWord_1062014, baseEnd_1062014] using wordTrace_append hprefix tailTrace_1062014
  have hstable : (prefixWord ++ tailWord_1062014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062014).length < 2 ^ (prefixWord ++ tailWord_1062014).sum := by decide
  have hdescent : baseEnd_1062014 < baseStart_1062014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062034 : List Nat := [3, 2, 3, 1, 1, 3, 1, 1, 2, 5]
def baseStart_1062034 : Nat := 118140960795 + 1062034 * 2 ^ 59
def prefixEnd_1062034 : Nat := 4983230072969 + 3 ^ 40 * 1062034 * 2
def baseEnd_1062034 : Nat := 363555942278135347193867

theorem tailTrace_1062034 : CollatzResearch.WordTrace tailWord_1062034 prefixEnd_1062034 363555942278135347193867 := by
  unfold tailWord_1062034
  simp only [CollatzResearch.WordTrace]
  refine ⟨9683890558609918452958289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25823708156293115874555437 9683890558609918452958289)
  ·
    refine ⟨7262917918957438839718717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9683890558609918452958289 7262917918957438839718717)
    ·
      refine ⟨2723594219609039564894519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7262917918957438839718717 2723594219609039564894519)
      ·
        refine ⟨4085391329413559347341779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2723594219609039564894519 4085391329413559347341779)
        ·
          refine ⟨6128086994120339021012669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4085391329413559347341779 6128086994120339021012669)
          ·
            refine ⟨2298032622795127132879751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6128086994120339021012669 2298032622795127132879751)
            ·
              refine ⟨3447048934192690699319627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2298032622795127132879751 3447048934192690699319627)
              ·
                refine ⟨5170573401289036048979441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3447048934192690699319627 5170573401289036048979441)
                ·
                  refine ⟨3877930050966777036734581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5170573401289036048979441 3877930050966777036734581)
                  ·
                    refine ⟨363555942278135347193867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3877930050966777036734581 363555942278135347193867)
                    ·
                      rfl

theorem cell22_1062034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_1062034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1062034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1062034 prefixEnd_1062034 := by exact prefixLift 1062034
  have htrace : WordTrace (prefixWord ++ tailWord_1062034) baseStart_1062034 baseEnd_1062034 := by
    simpa [prefixWord, tailWord_1062034, baseEnd_1062034] using wordTrace_append hprefix tailTrace_1062034
  have hstable : (prefixWord ++ tailWord_1062034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062034).length < 2 ^ (prefixWord ++ tailWord_1062034).sum := by decide
  have hdescent : baseEnd_1062034 < baseStart_1062034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062049 : List Nat := [1, 2, 3, 3, 1, 1, 2, 4, 1, 4]
def baseStart_1062049 : Nat := 118140960795 + 1062049 * 2 ^ 59
def prefixEnd_1062049 : Nat := 4983230072969 + 3 ^ 40 * 1062049 * 2
def baseEnd_1062049 : Nat := 363561077084680308068821

theorem tailTrace_1062049 : CollatzResearch.WordTrace tailWord_1062049 prefixEnd_1062049 363561077084680308068821 := by
  unfold tailWord_1062049
  simp only [CollatzResearch.WordTrace]
  refine ⟨38736109329385331373629201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25824072886256887582419467 38736109329385331373629201)
  ·
    refine ⟨29052081997038998530221901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38736109329385331373629201 29052081997038998530221901)
    ·
      refine ⟨10894530748889624448833213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29052081997038998530221901 10894530748889624448833213)
      ·
        refine ⟨4085449030833609168312455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10894530748889624448833213 4085449030833609168312455)
        ·
          refine ⟨6128173546250413752468683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4085449030833609168312455 6128173546250413752468683)
          ·
            refine ⟨9192260319375620628703025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6128173546250413752468683 9192260319375620628703025)
            ·
              refine ⟨6894195239531715471527269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9192260319375620628703025 6894195239531715471527269)
              ·
                refine ⟨1292661607412196650911363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6894195239531715471527269 1292661607412196650911363)
                ·
                  refine ⟨1938992411118294976367045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1292661607412196650911363 1938992411118294976367045)
                  ·
                    refine ⟨363561077084680308068821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1938992411118294976367045 363561077084680308068821)
                    ·
                      rfl

theorem cell22_1062049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_1062049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1062049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1062049 prefixEnd_1062049 := by exact prefixLift 1062049
  have htrace : WordTrace (prefixWord ++ tailWord_1062049) baseStart_1062049 baseEnd_1062049 := by
    simpa [prefixWord, tailWord_1062049, baseEnd_1062049] using wordTrace_append hprefix tailTrace_1062049
  have hstable : (prefixWord ++ tailWord_1062049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062049).length < 2 ^ (prefixWord ++ tailWord_1062049).sum := by decide
  have hdescent : baseEnd_1062049 < baseStart_1062049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062066 : List Nat := [3, 2, 1, 1, 1, 4, 4, 1, 1, 4]
def baseStart_1062066 : Nat := 118140960795 + 1062066 * 2 ^ 59
def prefixEnd_1062066 : Nat := 4983230072969 + 3 ^ 40 * 1062066 * 2
def baseEnd_1062066 : Nat := 363566896532097930393769

theorem tailTrace_1062066 : CollatzResearch.WordTrace tailWord_1062066 prefixEnd_1062066 363566896532097930393769 := by
  unfold tailWord_1062066
  simp only [CollatzResearch.WordTrace]
  refine ⟨9684182342580935819249513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25824486246882495517998701 9684182342580935819249513)
  ·
    refine ⟨7263136756935701864437135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9684182342580935819249513 7263136756935701864437135)
    ·
      refine ⟨10894705135403552796655703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7263136756935701864437135 10894705135403552796655703)
      ·
        refine ⟨16342057703105329194983555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10894705135403552796655703 16342057703105329194983555)
        ·
          refine ⟨24513086554657993792475333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16342057703105329194983555 24513086554657993792475333)
          ·
            refine ⟨4596203728998373836089125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24513086554657993792475333 4596203728998373836089125)
            ·
              refine ⟨861788199187195094266711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4596203728998373836089125 861788199187195094266711)
              ·
                refine ⟨1292682298780792641400067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 861788199187195094266711 1292682298780792641400067)
                ·
                  refine ⟨1939023448171188962100101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1292682298780792641400067 1939023448171188962100101)
                  ·
                    refine ⟨363566896532097930393769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1939023448171188962100101 363566896532097930393769)
                    ·
                      rfl

theorem cell22_1062066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 1, 1, 4].length) (baseStart_1062066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1062066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1062066 prefixEnd_1062066 := by exact prefixLift 1062066
  have htrace : WordTrace (prefixWord ++ tailWord_1062066) baseStart_1062066 baseEnd_1062066 := by
    simpa [prefixWord, tailWord_1062066, baseEnd_1062066] using wordTrace_append hprefix tailTrace_1062066
  have hstable : (prefixWord ++ tailWord_1062066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062066).length < 2 ^ (prefixWord ++ tailWord_1062066).sum := by decide
  have hdescent : baseEnd_1062066 < baseStart_1062066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062070 : List Nat := [5, 1, 3, 2, 1, 2, 1, 2, 5]
def baseStart_1062070 : Nat := 118140960795 + 1062070 * 2 ^ 59
def prefixEnd_1062070 : Nat := 4983230072969 + 3 ^ 40 * 1062070 * 2
def baseEnd_1062070 : Nat := 121189421937947751097919

theorem tailTrace_1062070 : CollatzResearch.WordTrace tailWord_1062070 prefixEnd_1062070 121189421937947751097919 := by
  unfold tailWord_1062070
  simp only [CollatzResearch.WordTrace]
  refine ⟨2421054703894328247508979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25824583508206167973429109 2421054703894328247508979)
  ·
    refine ⟨3631582055841492371263469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2421054703894328247508979 3631582055841492371263469)
    ·
      refine ⟨1361843270940559639223801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3631582055841492371263469 1361843270940559639223801)
      ·
        refine ⟨1021382453205419729417851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1361843270940559639223801 1021382453205419729417851)
        ·
          refine ⟨1532073679808129594126777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1021382453205419729417851 1532073679808129594126777)
          ·
            refine ⟨1149055259856097195595083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1532073679808129594126777 1149055259856097195595083)
            ·
              refine ⟨1723582889784145793392625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1149055259856097195595083 1723582889784145793392625)
              ·
                refine ⟨1292687167338109345044469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1723582889784145793392625 1292687167338109345044469)
                ·
                  refine ⟨121189421937947751097919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1292687167338109345044469 121189421937947751097919)
                  ·
                    rfl

theorem cell22_1062070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_1062070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1062070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1062070 prefixEnd_1062070 := by exact prefixLift 1062070
  have htrace : WordTrace (prefixWord ++ tailWord_1062070) baseStart_1062070 baseEnd_1062070 := by
    simpa [prefixWord, tailWord_1062070, baseEnd_1062070] using wordTrace_append hprefix tailTrace_1062070
  have hstable : (prefixWord ++ tailWord_1062070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062070).length < 2 ^ (prefixWord ++ tailWord_1062070).sum := by decide
  have hdescent : baseEnd_1062070 < baseStart_1062070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062081 : List Nat := [1, 2, 6, 1, 1, 2, 2, 1, 6]
def baseStart_1062081 : Nat := 118140960795 + 1062081 * 2 ^ 59
def prefixEnd_1062081 : Nat := 4983230072969 + 3 ^ 40 * 1062081 * 2
def baseEnd_1062081 : Nat := 121190677112880963756241

theorem tailTrace_1062081 : CollatzResearch.WordTrace tailWord_1062081 prefixEnd_1062081 121190677112880963756241 := by
  unfold tailWord_1062081
  simp only [CollatzResearch.WordTrace]
  refine ⟨38737276465269400838794097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25824850976846267225862731 38737276465269400838794097)
  ·
    refine ⟨29052957348952050629095573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38737276465269400838794097 29052957348952050629095573)
    ·
      refine ⟨1361857375732127373238855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 29052957348952050629095573 1361857375732127373238855)
      ·
        refine ⟨2042786063598191059858283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1361857375732127373238855 2042786063598191059858283)
        ·
          refine ⟨3064179095397286589787425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2042786063598191059858283 3064179095397286589787425)
          ·
            refine ⟨2298134321547964942340569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3064179095397286589787425 2298134321547964942340569)
            ·
              refine ⟨1723600741160973706755427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2298134321547964942340569 1723600741160973706755427)
              ·
                refine ⟨2585401111741460560133141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1723600741160973706755427 2585401111741460560133141)
                ·
                  refine ⟨121190677112880963756241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2585401111741460560133141 121190677112880963756241)
                  ·
                    rfl

theorem cell22_1062081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 6].length) (baseStart_1062081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1062081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1062081 prefixEnd_1062081 := by exact prefixLift 1062081
  have htrace : WordTrace (prefixWord ++ tailWord_1062081) baseStart_1062081 baseEnd_1062081 := by
    simpa [prefixWord, tailWord_1062081, baseEnd_1062081] using wordTrace_append hprefix tailTrace_1062081
  have hstable : (prefixWord ++ tailWord_1062081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062081).length < 2 ^ (prefixWord ++ tailWord_1062081).sum := by decide
  have hdescent : baseEnd_1062081 < baseStart_1062081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062132 : List Nat := [2, 6, 1, 2, 2, 1, 1, 1, 6]
def baseStart_1062132 : Nat := 118140960795 + 1062132 * 2 ^ 59
def prefixEnd_1062132 : Nat := 4983230072969 + 3 ^ 40 * 1062132 * 2
def baseEnd_1062132 : Nat := 121196496560298586081189

theorem tailTrace_1062132 : CollatzResearch.WordTrace tailWord_1062132 prefixEnd_1062132 121196496560298586081189 := by
  unfold tailWord_1062132
  simp only [CollatzResearch.WordTrace]
  refine ⟨19369568294042318274450325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25826091058723091032600433 19369568294042318274450325)
  ·
    refine ⟨907948513783233669114859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19369568294042318274450325 907948513783233669114859)
    ·
      refine ⟨1361922770674850503672289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 907948513783233669114859 1361922770674850503672289)
      ·
        refine ⟨1021442078006137877754217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1361922770674850503672289 1021442078006137877754217)
        ·
          refine ⟨766081558504603408315663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1021442078006137877754217 766081558504603408315663)
          ·
            refine ⟨1149122337756905112473495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 766081558504603408315663 1149122337756905112473495)
            ·
              refine ⟨1723683506635357668710243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1149122337756905112473495 1723683506635357668710243)
              ·
                refine ⟨2585525259953036503065365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1723683506635357668710243 2585525259953036503065365)
                ·
                  refine ⟨121196496560298586081189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2585525259953036503065365 121196496560298586081189)
                  ·
                    rfl

theorem cell22_1062132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_1062132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1062132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1062132 prefixEnd_1062132 := by exact prefixLift 1062132
  have htrace : WordTrace (prefixWord ++ tailWord_1062132) baseStart_1062132 baseEnd_1062132 := by
    simpa [prefixWord, tailWord_1062132, baseEnd_1062132] using wordTrace_append hprefix tailTrace_1062132
  have hstable : (prefixWord ++ tailWord_1062132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062132).length < 2 ^ (prefixWord ++ tailWord_1062132).sum := by decide
  have hdescent : baseEnd_1062132 < baseStart_1062132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062137 : List Nat := [1, 2, 1, 3, 1, 1, 3, 3, 7]
def baseStart_1062137 : Nat := 118140960795 + 1062137 * 2 ^ 59
def prefixEnd_1062137 : Nat := 4983230072969 + 3 ^ 40 * 1062137 * 2
def baseEnd_1062137 : Nat := 121197067094359137289517

theorem tailTrace_1062137 : CollatzResearch.WordTrace tailWord_1062137 prefixEnd_1062137 121197067094359137289517 := by
  unfold tailWord_1062137
  simp only [CollatzResearch.WordTrace]
  refine ⟨38739318953066522402832665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25826212635377681601888443 38739318953066522402832665)
  ·
    refine ⟨29054489214799891802124499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38739318953066522402832665 29054489214799891802124499)
    ·
      refine ⟨43581733822199837703186749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29054489214799891802124499 43581733822199837703186749)
      ·
        refine ⟨16343150183324939138695031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43581733822199837703186749 16343150183324939138695031)
        ·
          refine ⟨24514725274987408708042547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16343150183324939138695031 24514725274987408708042547)
          ·
            refine ⟨36772087912481113062063821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24514725274987408708042547 36772087912481113062063821)
            ·
              refine ⟨13789532967180417398273933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36772087912481113062063821 13789532967180417398273933)
              ·
                refine ⟨5171074862692656524352725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13789532967180417398273933 5171074862692656524352725)
                ·
                  refine ⟨121197067094359137289517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5171074862692656524352725 121197067094359137289517)
                  ·
                    rfl

theorem cell22_1062137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 7].length) (baseStart_1062137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1062137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1062137 prefixEnd_1062137 := by exact prefixLift 1062137
  have htrace : WordTrace (prefixWord ++ tailWord_1062137) baseStart_1062137 baseEnd_1062137 := by
    simpa [prefixWord, tailWord_1062137, baseEnd_1062137] using wordTrace_append hprefix tailTrace_1062137
  have hstable : (prefixWord ++ tailWord_1062137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062137).length < 2 ^ (prefixWord ++ tailWord_1062137).sum := by decide
  have hdescent : baseEnd_1062137 < baseStart_1062137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062244 : List Nat := [2, 3, 1, 1, 3, 3, 9]
def baseStart_1062244 : Nat := 118140960795 + 1062244 * 2 ^ 59
def prefixEnd_1062244 : Nat := 4983230072969 + 3 ^ 40 * 1062244 * 2
def baseEnd_1062244 : Nat := 13467697391472770349749

theorem tailTrace_1062244 : CollatzResearch.WordTrace tailWord_1062244 prefixEnd_1062244 13467697391472770349749 := by
  unfold tailWord_1062244
  simp only [CollatzResearch.WordTrace]
  refine ⟨19371610781839439838488893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25828814375785919784651857 19371610781839439838488893)
  ·
    refine ⟨7264354043189789939433335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19371610781839439838488893 7264354043189789939433335)
    ·
      refine ⟨10896531064784684909150003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7264354043189789939433335 10896531064784684909150003)
      ·
        refine ⟨16344796597177027363725005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10896531064784684909150003 16344796597177027363725005)
        ·
          refine ⟨6129298723941385261396877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16344796597177027363725005 6129298723941385261396877)
          ·
            refine ⟨2298487021478019473023829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6129298723941385261396877 2298487021478019473023829)
            ·
              refine ⟨13467697391472770349749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2298487021478019473023829 13467697391472770349749)
              ·
                rfl

theorem cell22_1062244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 9].length) (baseStart_1062244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1062244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1062244 prefixEnd_1062244 := by exact prefixLift 1062244
  have htrace : WordTrace (prefixWord ++ tailWord_1062244) baseStart_1062244 baseEnd_1062244 := by
    simpa [prefixWord, tailWord_1062244, baseEnd_1062244] using wordTrace_append hprefix tailTrace_1062244
  have hstable : (prefixWord ++ tailWord_1062244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062244).length < 2 ^ (prefixWord ++ tailWord_1062244).sum := by decide
  have hdescent : baseEnd_1062244 < baseStart_1062244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062248 : List Nat := [2, 1, 4, 2, 3, 1, 1, 1, 4, 3]
def baseStart_1062248 : Nat := 118140960795 + 1062248 * 2 ^ 59
def prefixEnd_1062248 : Nat := 4983230072969 + 3 ^ 40 * 1062248 * 2
def baseEnd_1062248 : Nat := 363629198851510122343211

theorem tailTrace_1062248 : CollatzResearch.WordTrace tailWord_1062248 prefixEnd_1062248 363629198851510122343211 := by
  unfold tailWord_1062248
  simp only [CollatzResearch.WordTrace]
  refine ⟨19371683727832194180061699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25828911637109592240082265 19371683727832194180061699)
  ·
    refine ⟨29057525591748291270092549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19371683727832194180061699 29057525591748291270092549)
    ·
      refine ⟨5448286048452804613142353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29057525591748291270092549 5448286048452804613142353)
      ·
        refine ⟨4086214536339603459856765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5448286048452804613142353 4086214536339603459856765)
        ·
          refine ⟨1532330451127351297446287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4086214536339603459856765 1532330451127351297446287)
          ·
            refine ⟨2298495676691026946169431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1532330451127351297446287 2298495676691026946169431)
            ·
              refine ⟨3447743515036540419254147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2298495676691026946169431 3447743515036540419254147)
              ·
                refine ⟨5171615272554810628881221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3447743515036540419254147 5171615272554810628881221)
                ·
                  refine ⟨969677863604026992915229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5171615272554810628881221 969677863604026992915229)
                  ·
                    refine ⟨363629198851510122343211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 969677863604026992915229 363629198851510122343211)
                    ·
                      rfl

theorem cell22_1062248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_1062248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1062248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1062248 prefixEnd_1062248 := by exact prefixLift 1062248
  have htrace : WordTrace (prefixWord ++ tailWord_1062248) baseStart_1062248 baseEnd_1062248 := by
    simpa [prefixWord, tailWord_1062248, baseEnd_1062248] using wordTrace_append hprefix tailTrace_1062248
  have hstable : (prefixWord ++ tailWord_1062248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062248).length < 2 ^ (prefixWord ++ tailWord_1062248).sum := by decide
  have hdescent : baseEnd_1062248 < baseStart_1062248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062306 : List Nat := [3, 3, 1, 2, 1, 2, 2, 1, 7]
def baseStart_1062306 : Nat := 118140960795 + 1062306 * 2 ^ 59
def prefixEnd_1062306 : Nat := 4983230072969 + 3 ^ 40 * 1062306 * 2
def baseEnd_1062306 : Nat := 121216351145605768131011

theorem tailTrace_1062306 : CollatzResearch.WordTrace tailWord_1062306 prefixEnd_1062306 121216351145605768131011 := by
  unfold tailWord_1062306
  simp only [CollatzResearch.WordTrace]
  refine ⟨9686370722363566066433693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25830321926302842843823181 9686370722363566066433693)
  ·
    refine ⟨3632389020886337274912635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9686370722363566066433693 3632389020886337274912635)
    ·
      refine ⟨5448583531329505912368953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3632389020886337274912635 5448583531329505912368953)
      ·
        refine ⟨4086437648497129434276715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5448583531329505912368953 4086437648497129434276715)
        ·
          refine ⟨6129656472745694151415073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4086437648497129434276715 6129656472745694151415073)
          ·
            refine ⟨4597242354559270613561305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6129656472745694151415073 4597242354559270613561305)
            ·
              refine ⟨3447931765919452960170979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4597242354559270613561305 3447931765919452960170979)
              ·
                refine ⟨5171897648879179440256469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3447931765919452960170979 5171897648879179440256469)
                ·
                  refine ⟨121216351145605768131011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5171897648879179440256469 121216351145605768131011)
                  ·
                    rfl

theorem cell22_1062306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_1062306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1062306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1062306 prefixEnd_1062306 := by exact prefixLift 1062306
  have htrace : WordTrace (prefixWord ++ tailWord_1062306) baseStart_1062306 baseEnd_1062306 := by
    simpa [prefixWord, tailWord_1062306, baseEnd_1062306] using wordTrace_append hprefix tailTrace_1062306
  have hstable : (prefixWord ++ tailWord_1062306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062306).length < 2 ^ (prefixWord ++ tailWord_1062306).sum := by decide
  have hdescent : baseEnd_1062306 < baseStart_1062306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062379 : List Nat := [1, 1, 1, 1, 2, 3, 2, 11]
def baseStart_1062379 : Nat := 118140960795 + 1062379 * 2 ^ 59
def prefixEnd_1062379 : Nat := 4983230072969 + 3 ^ 40 * 1062379 * 2
def baseEnd_1062379 : Nat := 40408226980963271924201

theorem tailTrace_1062379 : CollatzResearch.WordTrace tailWord_1062379 prefixEnd_1062379 40408226980963271924201 := by
  unfold tailWord_1062379
  simp only [CollatzResearch.WordTrace]
  refine ⟨38748145418189797733142191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25832096945459865155428127 38748145418189797733142191)
  ·
    refine ⟨58122218127284696599713287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38748145418189797733142191 58122218127284696599713287)
    ·
      refine ⟨87183327190927044899569931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58122218127284696599713287 87183327190927044899569931)
      ·
        refine ⟨130774990786390567349354897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87183327190927044899569931 130774990786390567349354897)
        ·
          refine ⟨98081243089792925512016173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130774990786390567349354897 98081243089792925512016173)
          ·
            refine ⟨36780466158672347067006065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98081243089792925512016173 36780466158672347067006065)
            ·
              refine ⟨27585349619004260300254549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36780466158672347067006065 27585349619004260300254549)
              ·
                refine ⟨40408226980963271924201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 27585349619004260300254549 40408226980963271924201)
                ·
                  rfl

theorem cell22_1062379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 11].length) (baseStart_1062379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1062379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1062379 prefixEnd_1062379 := by exact prefixLift 1062379
  have htrace : WordTrace (prefixWord ++ tailWord_1062379) baseStart_1062379 baseEnd_1062379 := by
    simpa [prefixWord, tailWord_1062379, baseEnd_1062379] using wordTrace_append hprefix tailTrace_1062379
  have hstable : (prefixWord ++ tailWord_1062379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062379).length < 2 ^ (prefixWord ++ tailWord_1062379).sum := by decide
  have hdescent : baseEnd_1062379 < baseStart_1062379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062383 : List Nat := [1, 1, 2, 1, 4, 1, 4, 3, 2, 3]
def baseStart_1062383 : Nat := 118140960795 + 1062383 * 2 ^ 59
def prefixEnd_1062383 : Nat := 4983230072969 + 3 ^ 40 * 1062383 * 2
def baseEnd_1062383 : Nat := 363675412110414770217797

theorem tailTrace_1062383 : CollatzResearch.WordTrace tailWord_1062383 prefixEnd_1062383 363675412110414770217797 := by
  unfold tailWord_1062383
  simp only [CollatzResearch.WordTrace]
  refine ⟨38748291310175306416287803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25832194206783537610858535 38748291310175306416287803)
  ·
    refine ⟨58122436965262959624431705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38748291310175306416287803 58122436965262959624431705)
    ·
      refine ⟨43591827723947219718323779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58122436965262959624431705 43591827723947219718323779)
      ·
        refine ⟨65387741585920829577485669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43591827723947219718323779 65387741585920829577485669)
        ·
          refine ⟨12260201547360155545778563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65387741585920829577485669 12260201547360155545778563)
          ·
            refine ⟨18390302321040233318667845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12260201547360155545778563 18390302321040233318667845)
            ·
              refine ⟨3448181685195043747250221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18390302321040233318667845 3448181685195043747250221)
              ·
                refine ⟨1293068131948141405218833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3448181685195043747250221 1293068131948141405218833)
                ·
                  refine ⟨969801098961106053914125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1293068131948141405218833 969801098961106053914125)
                  ·
                    refine ⟨363675412110414770217797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 969801098961106053914125 363675412110414770217797)
                    ·
                      rfl

theorem cell22_1062383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 3, 2, 3].length) (baseStart_1062383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1062383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1062383 prefixEnd_1062383 := by exact prefixLift 1062383
  have htrace : WordTrace (prefixWord ++ tailWord_1062383) baseStart_1062383 baseEnd_1062383 := by
    simpa [prefixWord, tailWord_1062383, baseEnd_1062383] using wordTrace_append hprefix tailTrace_1062383
  have hstable : (prefixWord ++ tailWord_1062383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062383).length < 2 ^ (prefixWord ++ tailWord_1062383).sum := by decide
  have hdescent : baseEnd_1062383 < baseStart_1062383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062402 : List Nat := [3, 4, 1, 2, 1, 2, 2, 3, 4]
def baseStart_1062402 : Nat := 118140960795 + 1062402 * 2 ^ 59
def prefixEnd_1062402 : Nat := 4983230072969 + 3 ^ 40 * 1062402 * 2
def baseEnd_1062402 : Nat := 121227305399568351330913

theorem tailTrace_1062402 : CollatzResearch.WordTrace tailWord_1062402 prefixEnd_1062402 121227305399568351330913 := by
  unfold tailWord_1062402
  simp only [CollatzResearch.WordTrace]
  refine ⟨9687246074276618165307365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25832656198070981774152973 9687246074276618165307365)
  ·
    refine ⟨1816358638926865905995131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9687246074276618165307365 1816358638926865905995131)
    ·
      refine ⟨2724537958390298858992697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1816358638926865905995131 2724537958390298858992697)
      ·
        refine ⟨2043403468792724144244523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2724537958390298858992697 2043403468792724144244523)
        ·
          refine ⟨3065105203189086216366785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2043403468792724144244523 3065105203189086216366785)
          ·
            refine ⟨2298828902391814662275089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3065105203189086216366785 2298828902391814662275089)
            ·
              refine ⟨1724121676793860996706317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2298828902391814662275089 1724121676793860996706317)
              ·
                refine ⟨646545628797697873764869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1724121676793860996706317 646545628797697873764869)
                ·
                  refine ⟨121227305399568351330913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 646545628797697873764869 121227305399568351330913)
                  ·
                    rfl

theorem cell22_1062402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_1062402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1062402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1062402 prefixEnd_1062402 := by exact prefixLift 1062402
  have htrace : WordTrace (prefixWord ++ tailWord_1062402) baseStart_1062402 baseEnd_1062402 := by
    simpa [prefixWord, tailWord_1062402, baseEnd_1062402] using wordTrace_append hprefix tailTrace_1062402
  have hstable : (prefixWord ++ tailWord_1062402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062402).length < 2 ^ (prefixWord ++ tailWord_1062402).sum := by decide
  have hdescent : baseEnd_1062402 < baseStart_1062402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062404 : List Nat := [2, 3, 2, 3, 3, 1, 2, 1, 1, 4]
def baseStart_1062404 : Nat := 118140960795 + 1062404 * 2 ^ 59
def prefixEnd_1062404 : Nat := 4983230072969 + 3 ^ 40 * 1062404 * 2
def baseEnd_1062404 : Nat := 363682600839577715442733

theorem tailTrace_1062404 : CollatzResearch.WordTrace tailWord_1062404 prefixEnd_1062404 363682600839577715442733 := by
  unfold tailWord_1062404
  simp only [CollatzResearch.WordTrace]
  refine ⟨19374528621549613501401133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25832704828732818001868177 19374528621549613501401133)
  ·
    refine ⟨7265448233081105063025425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19374528621549613501401133 7265448233081105063025425)
    ·
      refine ⟨5449086174810828797269069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7265448233081105063025425 5449086174810828797269069)
      ·
        refine ⟨2043407315554060798975901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5449086174810828797269069 2043407315554060798975901)
        ·
          refine ⟨766277743332772799615963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2043407315554060798975901 766277743332772799615963)
          ·
            refine ⟨1149416614999159199423945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 766277743332772799615963 1149416614999159199423945)
            ·
              refine ⟨862062461249369399567959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1149416614999159199423945 862062461249369399567959)
              ·
                refine ⟨1293093691874054099351939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 862062461249369399567959 1293093691874054099351939)
                ·
                  refine ⟨1939640537811081149027909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1293093691874054099351939 1939640537811081149027909)
                  ·
                    refine ⟨363682600839577715442733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1939640537811081149027909 363682600839577715442733)
                    ·
                      rfl

theorem cell22_1062404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_1062404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1062404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1062404 prefixEnd_1062404 := by exact prefixLift 1062404
  have htrace : WordTrace (prefixWord ++ tailWord_1062404) baseStart_1062404 baseEnd_1062404 := by
    simpa [prefixWord, tailWord_1062404, baseEnd_1062404] using wordTrace_append hprefix tailTrace_1062404
  have hstable : (prefixWord ++ tailWord_1062404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062404).length < 2 ^ (prefixWord ++ tailWord_1062404).sum := by decide
  have hdescent : baseEnd_1062404 < baseStart_1062404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062492 : List Nat := [2, 2, 4, 1, 2, 3, 2, 1, 5]
def baseStart_1062492 : Nat := 118140960795 + 1062492 * 2 ^ 59
def prefixEnd_1062492 : Nat := 4983230072969 + 3 ^ 40 * 1062492 * 2
def baseEnd_1062492 : Nat := 121237575012658273080821

theorem tailTrace_1062492 : CollatzResearch.WordTrace tailWord_1062492 prefixEnd_1062492 121237575012658273080821 := by
  unfold tailWord_1062492
  simp only [CollatzResearch.WordTrace]
  refine ⟨19376133433390209016002865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25834844577853612021337153 19376133433390209016002865)
  ·
    refine ⟨14532100075042656762002149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19376133433390209016002865 14532100075042656762002149)
    ·
      refine ⟨2724768764070498142875403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14532100075042656762002149 2724768764070498142875403)
      ·
        refine ⟨4087153146105747214313105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2724768764070498142875403 4087153146105747214313105)
        ·
          refine ⟨3065364859579310410734829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4087153146105747214313105 3065364859579310410734829)
          ·
            refine ⟨1149511822342241404025561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3065364859579310410734829 1149511822342241404025561)
            ·
              refine ⟨862133866756681053019171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1149511822342241404025561 862133866756681053019171)
              ·
                refine ⟨1293200800135021579528757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 862133866756681053019171 1293200800135021579528757)
                ·
                  refine ⟨121237575012658273080821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1293200800135021579528757 121237575012658273080821)
                  ·
                    rfl

theorem cell22_1062492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 1, 5].length) (baseStart_1062492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1062492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1062492 prefixEnd_1062492 := by exact prefixLift 1062492
  have htrace : WordTrace (prefixWord ++ tailWord_1062492) baseStart_1062492 baseEnd_1062492 := by
    simpa [prefixWord, tailWord_1062492, baseEnd_1062492] using wordTrace_append hprefix tailTrace_1062492
  have hstable : (prefixWord ++ tailWord_1062492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062492).length < 2 ^ (prefixWord ++ tailWord_1062492).sum := by decide
  have hdescent : baseEnd_1062492 < baseStart_1062492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062533 : List Nat := [1, 3, 1, 1, 4, 1, 1, 4, 2, 4]
def baseStart_1062533 : Nat := 118140960795 + 1062533 * 2 ^ 59
def prefixEnd_1062533 : Nat := 4983230072969 + 3 ^ 40 * 1062533 * 2
def baseEnd_1062533 : Nat := 363726760175864378967337

theorem tailTrace_1062533 : CollatzResearch.WordTrace tailWord_1062533 prefixEnd_1062533 363726760175864378967337 := by
  unfold tailWord_1062533
  simp only [CollatzResearch.WordTrace]
  refine ⟨38753762259631882034248253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25835841506421254689498835 38753762259631882034248253)
  ·
    refine ⟨14532660847361955762843095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38753762259631882034248253 14532660847361955762843095)
    ·
      refine ⟨21798991271042933644264643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14532660847361955762843095 21798991271042933644264643)
      ·
        refine ⟨32698486906564400466396965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21798991271042933644264643 32698486906564400466396965)
        ·
          refine ⟨6130966294980825087449431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32698486906564400466396965 6130966294980825087449431)
          ·
            refine ⟨9196449442471237631174147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6130966294980825087449431 9196449442471237631174147)
            ·
              refine ⟨13794674163706856446761221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9196449442471237631174147 13794674163706856446761221)
              ·
                refine ⟨2586501405695035583767729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13794674163706856446761221 2586501405695035583767729)
                ·
                  refine ⟨1939876054271276687825797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2586501405695035583767729 1939876054271276687825797)
                  ·
                    refine ⟨363726760175864378967337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1939876054271276687825797 363726760175864378967337)
                    ·
                      rfl

theorem cell22_1062533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 2, 4].length) (baseStart_1062533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1062533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1062533 prefixEnd_1062533 := by exact prefixLift 1062533
  have htrace : WordTrace (prefixWord ++ tailWord_1062533) baseStart_1062533 baseEnd_1062533 := by
    simpa [prefixWord, tailWord_1062533, baseEnd_1062533] using wordTrace_append hprefix tailTrace_1062533
  have hstable : (prefixWord ++ tailWord_1062533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062533).length < 2 ^ (prefixWord ++ tailWord_1062533).sum := by decide
  have hdescent : baseEnd_1062533 < baseStart_1062533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062535 : List Nat := [1, 1, 4, 2, 1, 3, 1, 4, 2, 3]
def baseStart_1062535 : Nat := 118140960795 + 1062535 * 2 ^ 59
def prefixEnd_1062535 : Nat := 4983230072969 + 3 ^ 40 * 1062535 * 2
def baseEnd_1062535 : Nat := 363727444816737040417331

theorem tailTrace_1062535 : CollatzResearch.WordTrace tailWord_1062535 prefixEnd_1062535 363727444816737040417331 := by
  unfold tailWord_1062535
  simp only [CollatzResearch.WordTrace]
  refine ⟨38753835205624636375821059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25835890137083090917214039 38753835205624636375821059)
  ·
    refine ⟨58130752808436954563731589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38753835205624636375821059 58130752808436954563731589)
    ·
      refine ⟨10899516151581928980699673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58130752808436954563731589 10899516151581928980699673)
      ·
        refine ⟨8174637113686446735524755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10899516151581928980699673 8174637113686446735524755)
        ·
          refine ⟨12261955670529670103287133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8174637113686446735524755 12261955670529670103287133)
          ·
            refine ⟨4598233376448626288732675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12261955670529670103287133 4598233376448626288732675)
            ·
              refine ⟨6897350064672939433099013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4598233376448626288732675 6897350064672939433099013)
              ·
                refine ⟨1293253137126176143706065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6897350064672939433099013 1293253137126176143706065)
                ·
                  refine ⟨969939852844632107779549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1293253137126176143706065 969939852844632107779549)
                  ·
                    refine ⟨363727444816737040417331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 969939852844632107779549 363727444816737040417331)
                    ·
                      rfl

theorem cell22_1062535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 4, 2, 3].length) (baseStart_1062535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1062535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1062535 prefixEnd_1062535 := by exact prefixLift 1062535
  have htrace : WordTrace (prefixWord ++ tailWord_1062535) baseStart_1062535 baseEnd_1062535 := by
    simpa [prefixWord, tailWord_1062535, baseEnd_1062535] using wordTrace_append hprefix tailTrace_1062535
  have hstable : (prefixWord ++ tailWord_1062535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062535).length < 2 ^ (prefixWord ++ tailWord_1062535).sum := by decide
  have hdescent : baseEnd_1062535 < baseStart_1062535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062653 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 5, 5]
def baseStart_1062653 : Nat := 118140960795 + 1062653 * 2 ^ 59
def prefixEnd_1062653 : Nat := 4983230072969 + 3 ^ 40 * 1062653 * 2
def baseEnd_1062653 : Nat := 363767838628224065966969

theorem tailTrace_1062653 : CollatzResearch.WordTrace tailWord_1062653 prefixEnd_1062653 363767838628224065966969 := by
  unfold tailWord_1062653
  simp only [CollatzResearch.WordTrace]
  refine ⟨38758139019197142528616613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25838759346131428352411075 38758139019197142528616613)
  ·
    refine ⟨7267151066099464224115615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38758139019197142528616613 7267151066099464224115615)
    ·
      refine ⟨10900726599149196336173423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7267151066099464224115615 10900726599149196336173423)
      ·
        refine ⟨16351089898723794504260135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10900726599149196336173423 16351089898723794504260135)
        ·
          refine ⟨24526634848085691756390203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16351089898723794504260135 24526634848085691756390203)
          ·
            refine ⟨36789952272128537634585305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24526634848085691756390203 36789952272128537634585305)
            ·
              refine ⟨27592464204096403225938979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36789952272128537634585305 27592464204096403225938979)
              ·
                refine ⟨41388696306144604838908469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27592464204096403225938979 41388696306144604838908469)
                ·
                  refine ⟨3880190278701056703647669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41388696306144604838908469 3880190278701056703647669)
                  ·
                    refine ⟨363767838628224065966969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3880190278701056703647669 363767838628224065966969)
                    ·
                      rfl

theorem cell22_1062653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_1062653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1062653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1062653 prefixEnd_1062653 := by exact prefixLift 1062653
  have htrace : WordTrace (prefixWord ++ tailWord_1062653) baseStart_1062653 baseEnd_1062653 := by
    simpa [prefixWord, tailWord_1062653, baseEnd_1062653] using wordTrace_append hprefix tailTrace_1062653
  have hstable : (prefixWord ++ tailWord_1062653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062653).length < 2 ^ (prefixWord ++ tailWord_1062653).sum := by decide
  have hdescent : baseEnd_1062653 < baseStart_1062653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062655 : List Nat := [1, 1, 2, 2, 1, 3, 2, 6, 4]
def baseStart_1062655 : Nat := 118140960795 + 1062655 * 2 ^ 59
def prefixEnd_1062655 : Nat := 4983230072969 + 3 ^ 40 * 1062655 * 2
def baseEnd_1062655 : Nat := 121256174423032242472321

theorem tailTrace_1062655 : CollatzResearch.WordTrace tailWord_1062655 prefixEnd_1062655 121256174423032242472321 := by
  unfold tailWord_1062655
  simp only [CollatzResearch.WordTrace]
  refine ⟨38758211965189896870189419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25838807976793264580126279 38758211965189896870189419)
  ·
    refine ⟨58137317947784845305284129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38758211965189896870189419 58137317947784845305284129)
    ·
      refine ⟨43602988460838633978963097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58137317947784845305284129 43602988460838633978963097)
      ·
        refine ⟨32702241345628975484222323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43602988460838633978963097 32702241345628975484222323)
        ·
          refine ⟨49053362018443463226333485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32702241345628975484222323 49053362018443463226333485)
          ·
            refine ⟨18395010756916298709875057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49053362018443463226333485 18395010756916298709875057)
            ·
              refine ⟨13796258067687224032406293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18395010756916298709875057 13796258067687224032406293)
              ·
                refine ⟨646699596922838626519045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13796258067687224032406293 646699596922838626519045)
                ·
                  refine ⟨121256174423032242472321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 646699596922838626519045 121256174423032242472321)
                  ·
                    rfl

theorem cell22_1062655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 6, 4].length) (baseStart_1062655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1062655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1062655 prefixEnd_1062655 := by exact prefixLift 1062655
  have htrace : WordTrace (prefixWord ++ tailWord_1062655) baseStart_1062655 baseEnd_1062655 := by
    simpa [prefixWord, tailWord_1062655, baseEnd_1062655] using wordTrace_append hprefix tailTrace_1062655
  have hstable : (prefixWord ++ tailWord_1062655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062655).length < 2 ^ (prefixWord ++ tailWord_1062655).sum := by decide
  have hdescent : baseEnd_1062655 < baseStart_1062655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062668 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 3, 6]
def baseStart_1062668 : Nat := 118140960795 + 1062668 * 2 ^ 59
def prefixEnd_1062668 : Nat := 4983230072969 + 3 ^ 40 * 1062668 * 2
def baseEnd_1062668 : Nat := 363772973434769026841923

theorem tailTrace_1062668 : CollatzResearch.WordTrace tailWord_1062668 prefixEnd_1062668 363772973434769026841923 := by
  unfold tailWord_1062668
  simp only [CollatzResearch.WordTrace]
  refine ⟨19379343057071400045206329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25839124076095200060275105 19379343057071400045206329)
  ·
    refine ⟨14534507292803550033904747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19379343057071400045206329 14534507292803550033904747)
    ·
      refine ⟨21801760939205325050857121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14534507292803550033904747 21801760939205325050857121)
      ·
        refine ⟨16351320704403993788142841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21801760939205325050857121 16351320704403993788142841)
        ·
          refine ⟨12263490528302995341107131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16351320704403993788142841 12263490528302995341107131)
          ·
            refine ⟨18395235792454493011660697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12263490528302995341107131 18395235792454493011660697)
            ·
              refine ⟨13796426844340869758745523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18395235792454493011660697 13796426844340869758745523)
              ·
                refine ⟨20694640266511304638118285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13796426844340869758745523 20694640266511304638118285)
                ·
                  refine ⟨7760490099941739239294357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20694640266511304638118285 7760490099941739239294357)
                  ·
                    refine ⟨363772973434769026841923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7760490099941739239294357 363772973434769026841923)
                    ·
                      rfl

theorem cell22_1062668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_1062668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1062668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1062668 prefixEnd_1062668 := by exact prefixLift 1062668
  have htrace : WordTrace (prefixWord ++ tailWord_1062668) baseStart_1062668 baseEnd_1062668 := by
    simpa [prefixWord, tailWord_1062668, baseEnd_1062668] using wordTrace_append hprefix tailTrace_1062668
  have hstable : (prefixWord ++ tailWord_1062668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062668).length < 2 ^ (prefixWord ++ tailWord_1062668).sum := by decide
  have hdescent : baseEnd_1062668 < baseStart_1062668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062674 : List Nat := [3, 2, 4, 1, 1, 1, 3, 2, 1, 4]
def baseStart_1062674 : Nat := 118140960795 + 1062674 * 2 ^ 59
def prefixEnd_1062674 : Nat := 4983230072969 + 3 ^ 40 * 1062674 * 2
def baseEnd_1062674 : Nat := 363775027357387011191905

theorem tailTrace_1062674 : CollatzResearch.WordTrace tailWord_1062674 prefixEnd_1062674 363775027357387011191905 := by
  unfold tailWord_1062674
  simp only [CollatzResearch.WordTrace]
  refine ⟨9689726238030265778782769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25839269968080708743420717 9689726238030265778782769)
  ·
    refine ⟨7267294678522699334087077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9689726238030265778782769 7267294678522699334087077)
    ·
      refine ⟨1362617752223006125141327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7267294678522699334087077 1362617752223006125141327)
      ·
        refine ⟨2043926628334509187711991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1362617752223006125141327 2043926628334509187711991)
        ·
          refine ⟨3065889942501763781567987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2043926628334509187711991 3065889942501763781567987)
          ·
            refine ⟨4598834913752645672351981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3065889942501763781567987 4598834913752645672351981)
            ·
              refine ⟨1724563092657242127131993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4598834913752645672351981 1724563092657242127131993)
              ·
                refine ⟨1293422319492931595348995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1724563092657242127131993 1293422319492931595348995)
                ·
                  refine ⟨1940133479239397393023493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1293422319492931595348995 1940133479239397393023493)
                  ·
                    refine ⟨363775027357387011191905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1940133479239397393023493 363775027357387011191905)
                    ·
                      rfl

theorem cell22_1062674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_1062674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1062674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1062674 prefixEnd_1062674 := by exact prefixLift 1062674
  have htrace : WordTrace (prefixWord ++ tailWord_1062674) baseStart_1062674 baseEnd_1062674 := by
    simpa [prefixWord, tailWord_1062674, baseEnd_1062674] using wordTrace_append hprefix tailTrace_1062674
  have hstable : (prefixWord ++ tailWord_1062674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062674).length < 2 ^ (prefixWord ++ tailWord_1062674).sum := by decide
  have hdescent : baseEnd_1062674 < baseStart_1062674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062717 : List Nat := [1, 4, 1, 4, 1, 3, 1, 7]
def baseStart_1062717 : Nat := 118140960795 + 1062717 * 2 ^ 59
def prefixEnd_1062717 : Nat := 4983230072969 + 3 ^ 40 * 1062717 * 2
def baseEnd_1062717 : Nat := 40421083015127692485197

theorem tailTrace_1062717 : CollatzResearch.WordTrace tailWord_1062717 prefixEnd_1062717 40421083015127692485197 := by
  unfold tailWord_1062717
  simp only [CollatzResearch.WordTrace]
  refine ⟨38760473290965281458946405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25840315527310187639297603 38760473290965281458946405)
  ·
    refine ⟨7267588742055990273552451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38760473290965281458946405 7267588742055990273552451)
    ·
      refine ⟨10901383113083985410328677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7267588742055990273552451 10901383113083985410328677)
      ·
        refine ⟨2044009333703247264436627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10901383113083985410328677 2044009333703247264436627)
        ·
          refine ⟨3066014000554870896654941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2044009333703247264436627 3066014000554870896654941)
          ·
            refine ⟨1149755250208076586245603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3066014000554870896654941 1149755250208076586245603)
            ·
              refine ⟨1724632875312114879368405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1149755250208076586245603 1724632875312114879368405)
              ·
                refine ⟨40421083015127692485197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1724632875312114879368405 40421083015127692485197)
                ·
                  rfl

theorem cell22_1062717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 7].length) (baseStart_1062717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1062717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1062717 prefixEnd_1062717 := by exact prefixLift 1062717
  have htrace : WordTrace (prefixWord ++ tailWord_1062717) baseStart_1062717 baseEnd_1062717 := by
    simpa [prefixWord, tailWord_1062717, baseEnd_1062717] using wordTrace_append hprefix tailTrace_1062717
  have hstable : (prefixWord ++ tailWord_1062717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062717).length < 2 ^ (prefixWord ++ tailWord_1062717).sum := by decide
  have hdescent : baseEnd_1062717 < baseStart_1062717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062760 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 4, 5]
def baseStart_1062760 : Nat := 118140960795 + 1062760 * 2 ^ 59
def prefixEnd_1062760 : Nat := 4983230072969 + 3 ^ 40 * 1062760 * 2
def baseEnd_1062760 : Nat := 363804466914911453541641

theorem tailTrace_1062760 : CollatzResearch.WordTrace tailWord_1062760 prefixEnd_1062760 363804466914911453541641 := by
  unfold tailWord_1062760
  simp only [CollatzResearch.WordTrace]
  refine ⟨19381020814904749901380867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25841361086539666535174489 19381020814904749901380867)
  ·
    refine ⟨29071531222357124852071301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19381020814904749901380867 29071531222357124852071301)
    ·
      refine ⟨5450912104191960909763369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29071531222357124852071301 5450912104191960909763369)
      ·
        refine ⟨4088184078143970682322527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5450912104191960909763369 4088184078143970682322527)
        ·
          refine ⟨6132276117215956023483791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4088184078143970682322527 6132276117215956023483791)
          ·
            refine ⟨9198414175823934035225687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6132276117215956023483791 9198414175823934035225687)
            ·
              refine ⟨13797621263735901052838531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9198414175823934035225687 13797621263735901052838531)
              ·
                refine ⟨20696431895603851579257797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13797621263735901052838531 20696431895603851579257797)
                ·
                  refine ⟨3880580980425722171110837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20696431895603851579257797 3880580980425722171110837)
                  ·
                    refine ⟨363804466914911453541641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3880580980425722171110837 363804466914911453541641)
                    ·
                      rfl

theorem cell22_1062760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_1062760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1062760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1062760 prefixEnd_1062760 := by exact prefixLift 1062760
  have htrace : WordTrace (prefixWord ++ tailWord_1062760) baseStart_1062760 baseEnd_1062760 := by
    simpa [prefixWord, tailWord_1062760, baseEnd_1062760] using wordTrace_append hprefix tailTrace_1062760
  have hstable : (prefixWord ++ tailWord_1062760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062760).length < 2 ^ (prefixWord ++ tailWord_1062760).sum := by decide
  have hdescent : baseEnd_1062760 < baseStart_1062760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062766 : List Nat := [4, 1, 2, 3, 1, 1, 2, 4, 1, 3]
def baseStart_1062766 : Nat := 118140960795 + 1062766 * 2 ^ 59
def prefixEnd_1062766 : Nat := 4983230072969 + 3 ^ 40 * 1062766 * 2
def baseEnd_1062766 : Nat := 363806520837529437891623

theorem tailTrace_1062766 : CollatzResearch.WordTrace tailWord_1062766 prefixEnd_1062766 363806520837529437891623 := by
  unfold tailWord_1062766
  simp only [CollatzResearch.WordTrace]
  refine ⟨4845282558473470353435019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25841506978525175218320101 4845282558473470353435019)
  ·
    refine ⟨7267923837710205530152529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4845282558473470353435019 7267923837710205530152529)
    ·
      refine ⟨5450942878282654147614397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7267923837710205530152529 5450942878282654147614397)
      ·
        refine ⟨2044103579355995305355399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5450942878282654147614397 2044103579355995305355399)
        ·
          refine ⟨3066155369033992958033099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2044103579355995305355399 3066155369033992958033099)
          ·
            refine ⟨4599233053550989437049649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3066155369033992958033099 4599233053550989437049649)
            ·
              refine ⟨3449424790163242077787237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4599233053550989437049649 3449424790163242077787237)
              ·
                refine ⟨646767148155607889585107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3449424790163242077787237 646767148155607889585107)
                ·
                  refine ⟨970150722233411834377661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 646767148155607889585107 970150722233411834377661)
                  ·
                    refine ⟨363806520837529437891623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 970150722233411834377661 363806520837529437891623)
                    ·
                      rfl

theorem cell22_1062766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_1062766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1062766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1062766 prefixEnd_1062766 := by exact prefixLift 1062766
  have htrace : WordTrace (prefixWord ++ tailWord_1062766) baseStart_1062766 baseEnd_1062766 := by
    simpa [prefixWord, tailWord_1062766, baseEnd_1062766] using wordTrace_append hprefix tailTrace_1062766
  have hstable : (prefixWord ++ tailWord_1062766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062766).length < 2 ^ (prefixWord ++ tailWord_1062766).sum := by decide
  have hdescent : baseEnd_1062766 < baseStart_1062766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062805 : List Nat := [1, 3, 2, 1, 1, 3, 2, 1, 3, 5]
def baseStart_1062805 : Nat := 118140960795 + 1062805 * 2 ^ 59
def prefixEnd_1062805 : Nat := 4983230072969 + 3 ^ 40 * 1062805 * 2
def baseEnd_1062805 : Nat := 363819871334546336166503

theorem tailTrace_1062805 : CollatzResearch.WordTrace tailWord_1062805 prefixEnd_1062805 363819871334546336166503 := by
  unfold tailWord_1062805
  simp only [CollatzResearch.WordTrace]
  refine ⟨38763682914646472488149869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25842455276430981658766579 38763682914646472488149869)
  ·
    refine ⟨14536381092992427183056201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38763682914646472488149869 14536381092992427183056201)
    ·
      refine ⟨10902285819744320387292151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14536381092992427183056201 10902285819744320387292151)
      ·
        refine ⟨16353428729616480580938227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10902285819744320387292151 16353428729616480580938227)
        ·
          refine ⟨24530143094424720871407341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16353428729616480580938227 24530143094424720871407341)
          ·
            refine ⟨9198803660409270326777753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24530143094424720871407341 9198803660409270326777753)
            ·
              refine ⟨6899102745306952745083315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9198803660409270326777753 6899102745306952745083315)
              ·
                refine ⟨10348654117960429117624973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6899102745306952745083315 10348654117960429117624973)
                ·
                  refine ⟨3880745294235160919109365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10348654117960429117624973 3880745294235160919109365)
                  ·
                    refine ⟨363819871334546336166503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3880745294235160919109365 363819871334546336166503)
                    ·
                      rfl

theorem cell22_1062805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_1062805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1062805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1062805 prefixEnd_1062805 := by exact prefixLift 1062805
  have htrace : WordTrace (prefixWord ++ tailWord_1062805) baseStart_1062805 baseEnd_1062805 := by
    simpa [prefixWord, tailWord_1062805, baseEnd_1062805] using wordTrace_append hprefix tailTrace_1062805
  have hstable : (prefixWord ++ tailWord_1062805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062805).length < 2 ^ (prefixWord ++ tailWord_1062805).sum := by decide
  have hdescent : baseEnd_1062805 < baseStart_1062805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062830 : List Nat := [4, 1, 5, 1, 1, 2, 2, 1, 5]
def baseStart_1062830 : Nat := 118140960795 + 1062830 * 2 ^ 59
def prefixEnd_1062830 : Nat := 4983230072969 + 3 ^ 40 * 1062830 * 2
def baseEnd_1062830 : Nat := 121276143115151534763809

theorem tailTrace_1062830 : CollatzResearch.WordTrace tailWord_1062830 prefixEnd_1062830 121276143115151534763809 := by
  unfold tailWord_1062830
  simp only [CollatzResearch.WordTrace]
  refine ⟨4845574342444487719726243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25843063159703934505206629 4845574342444487719726243)
  ·
    refine ⟨7268361513666731579589365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4845574342444487719726243 7268361513666731579589365)
    ·
      refine ⟨681408891906256085586503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7268361513666731579589365 681408891906256085586503)
      ·
        refine ⟨1022113337859384128379755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 681408891906256085586503 1022113337859384128379755)
        ·
          refine ⟨1533170006789076192569633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1022113337859384128379755 1533170006789076192569633)
          ·
            refine ⟨1149877505091807144427225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1533170006789076192569633 1149877505091807144427225)
            ·
              refine ⟨862408128818855358320419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1149877505091807144427225 862408128818855358320419)
              ·
                refine ⟨1293612193228283037480629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 862408128818855358320419 1293612193228283037480629)
                ·
                  refine ⟨121276143115151534763809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1293612193228283037480629 121276143115151534763809)
                  ·
                    rfl

theorem cell22_1062830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 1, 5].length) (baseStart_1062830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1062830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1062830 prefixEnd_1062830 := by exact prefixLift 1062830
  have htrace : WordTrace (prefixWord ++ tailWord_1062830) baseStart_1062830 baseEnd_1062830 := by
    simpa [prefixWord, tailWord_1062830, baseEnd_1062830] using wordTrace_append hprefix tailTrace_1062830
  have hstable : (prefixWord ++ tailWord_1062830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062830).length < 2 ^ (prefixWord ++ tailWord_1062830).sum := by decide
  have hdescent : baseEnd_1062830 < baseStart_1062830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062835 : List Nat := [1, 1, 1, 2, 3, 1, 6, 7]
def baseStart_1062835 : Nat := 118140960795 + 1062835 * 2 ^ 59
def prefixEnd_1062835 : Nat := 4983230072969 + 3 ^ 40 * 1062835 * 2
def baseEnd_1062835 : Nat := 40425571216404028657379

theorem tailTrace_1062835 : CollatzResearch.WordTrace tailWord_1062835 prefixEnd_1062835 40425571216404028657379 := by
  unfold tailWord_1062835
  simp only [CollatzResearch.WordTrace]
  refine ⟨38764777104537787611741959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25843184736358525074494639 38764777104537787611741959)
  ·
    refine ⟨58147165656806681417612939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38764777104537787611741959 58147165656806681417612939)
    ·
      refine ⟨87220748485210022126419409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58147165656806681417612939 87220748485210022126419409)
      ·
        refine ⟨65415561363907516594814557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87220748485210022126419409 65415561363907516594814557)
        ·
          refine ⟨24530835511465318723055459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65415561363907516594814557 24530835511465318723055459)
          ·
            refine ⟨36796253267197978084583189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24530835511465318723055459 36796253267197978084583189)
            ·
              refine ⟨1724824371899905222714837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36796253267197978084583189 1724824371899905222714837)
              ·
                refine ⟨40425571216404028657379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1724824371899905222714837 40425571216404028657379)
                ·
                  rfl

theorem cell22_1062835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 7].length) (baseStart_1062835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1062835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1062835 prefixEnd_1062835 := by exact prefixLift 1062835
  have htrace : WordTrace (prefixWord ++ tailWord_1062835) baseStart_1062835 baseEnd_1062835 := by
    simpa [prefixWord, tailWord_1062835, baseEnd_1062835] using wordTrace_append hprefix tailTrace_1062835
  have hstable : (prefixWord ++ tailWord_1062835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062835).length < 2 ^ (prefixWord ++ tailWord_1062835).sum := by decide
  have hdescent : baseEnd_1062835 < baseStart_1062835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062880 : List Nat := [2, 1, 1, 3, 1, 1, 1, 5, 7]
def baseStart_1062880 : Nat := 118140960795 + 1062880 * 2 ^ 59
def prefixEnd_1062880 : Nat := 4983230072969 + 3 ^ 40 * 1062880 * 2
def baseEnd_1062880 : Nat := 121281848455757046847091

theorem tailTrace_1062880 : CollatzResearch.WordTrace tailWord_1062880 prefixEnd_1062880 121281848455757046847091 := by
  unfold tailWord_1062880
  simp only [CollatzResearch.WordTrace]
  refine ⟨19383209194687380148565047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25844278926249840198086729 19383209194687380148565047)
  ·
    refine ⟨29074813792031070222847571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19383209194687380148565047 29074813792031070222847571)
    ·
      refine ⟨43612220688046605334271357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29074813792031070222847571 43612220688046605334271357)
      ·
        refine ⟨16354582758017477000351759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43612220688046605334271357 16354582758017477000351759)
        ·
          refine ⟨24531874137026215500527639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16354582758017477000351759 24531874137026215500527639)
          ·
            refine ⟨36797811205539323250791459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24531874137026215500527639 36797811205539323250791459)
            ·
              refine ⟨55196716808308984876187189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36797811205539323250791459 55196716808308984876187189)
              ·
                refine ⟨5174692200778967332142549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55196716808308984876187189 5174692200778967332142549)
                ·
                  refine ⟨121281848455757046847091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5174692200778967332142549 121281848455757046847091)
                  ·
                    rfl

theorem cell22_1062880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 7].length) (baseStart_1062880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1062880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1062880 prefixEnd_1062880 := by exact prefixLift 1062880
  have htrace : WordTrace (prefixWord ++ tailWord_1062880) baseStart_1062880 baseEnd_1062880 := by
    simpa [prefixWord, tailWord_1062880, baseEnd_1062880] using wordTrace_append hprefix tailTrace_1062880
  have hstable : (prefixWord ++ tailWord_1062880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062880).length < 2 ^ (prefixWord ++ tailWord_1062880).sum := by decide
  have hdescent : baseEnd_1062880 < baseStart_1062880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062972 : List Nat := [2, 2, 2, 2, 2, 1, 1, 3, 1, 6]
def baseStart_1062972 : Nat := 118140960795 + 1062972 * 2 ^ 59
def prefixEnd_1062972 : Nat := 4983230072969 + 3 ^ 40 * 1062972 * 2
def baseEnd_1062972 : Nat := 363877038847413567240991

theorem tailTrace_1062972 : CollatzResearch.WordTrace tailWord_1062972 prefixEnd_1062972 363877038847413567240991 := by
  unfold tailWord_1062972
  simp only [CollatzResearch.WordTrace]
  refine ⟨19384886952520730004739585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25846515936694306672986113 19384886952520730004739585)
  ·
    refine ⟨14538665214390547503554689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19384886952520730004739585 14538665214390547503554689)
    ·
      refine ⟨10903998910792910627666017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14538665214390547503554689 10903998910792910627666017)
      ·
        refine ⟨8177999183094682970749513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10903998910792910627666017 8177999183094682970749513)
        ·
          refine ⟨6133499387321012228062135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8177999183094682970749513 6133499387321012228062135)
          ·
            refine ⟨9200249080981518342093203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6133499387321012228062135 9200249080981518342093203)
            ·
              refine ⟨13800373621472277513139805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9200249080981518342093203 13800373621472277513139805)
              ·
                refine ⟨5175140108052104067427427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13800373621472277513139805 5175140108052104067427427)
                ·
                  refine ⟨7762710162078156101141141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5175140108052104067427427 7762710162078156101141141)
                  ·
                    refine ⟨363877038847413567240991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7762710162078156101141141 363877038847413567240991)
                    ·
                      rfl

theorem cell22_1062972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_1062972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1062972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1062972 prefixEnd_1062972 := by exact prefixLift 1062972
  have htrace : WordTrace (prefixWord ++ tailWord_1062972) baseStart_1062972 baseEnd_1062972 := by
    simpa [prefixWord, tailWord_1062972, baseEnd_1062972] using wordTrace_append hprefix tailTrace_1062972
  have hstable : (prefixWord ++ tailWord_1062972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062972).length < 2 ^ (prefixWord ++ tailWord_1062972).sum := by decide
  have hdescent : baseEnd_1062972 < baseStart_1062972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062976 : List Nat := [2, 1, 1, 2, 2, 6, 1, 3, 4]
def baseStart_1062976 : Nat := 118140960795 + 1062976 * 2 ^ 59
def prefixEnd_1062976 : Nat := 4983230072969 + 3 ^ 40 * 1062976 * 2
def baseEnd_1062976 : Nat := 121292802709719630046993

theorem tailTrace_1062976 : CollatzResearch.WordTrace tailWord_1062976 prefixEnd_1062976 121292802709719630046993 := by
  unfold tailWord_1062976
  simp only [CollatzResearch.WordTrace]
  refine ⟨19384959898513484346312391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25846613198017979128416521 19384959898513484346312391)
  ·
    refine ⟨29077439847770226519468587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19384959898513484346312391 29077439847770226519468587)
    ·
      refine ⟨43616159771655339779202881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29077439847770226519468587 43616159771655339779202881)
      ·
        refine ⟨32712119828741504834402161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43616159771655339779202881 32712119828741504834402161)
        ·
          refine ⟨24534089871556128625801621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32712119828741504834402161 24534089871556128625801621)
          ·
            refine ⟨1150035462729193529334451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24534089871556128625801621 1150035462729193529334451)
            ·
              refine ⟨1725053194093790294001677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1150035462729193529334451 1725053194093790294001677)
              ·
                refine ⟨646894947785171360250629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1725053194093790294001677 646894947785171360250629)
                ·
                  refine ⟨121292802709719630046993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 646894947785171360250629 121292802709719630046993)
                  ·
                    rfl

theorem cell22_1062976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 3, 4].length) (baseStart_1062976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1062976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1062976 prefixEnd_1062976 := by exact prefixLift 1062976
  have htrace : WordTrace (prefixWord ++ tailWord_1062976) baseStart_1062976 baseEnd_1062976 := by
    simpa [prefixWord, tailWord_1062976, baseEnd_1062976] using wordTrace_append hprefix tailTrace_1062976
  have hstable : (prefixWord ++ tailWord_1062976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062976).length < 2 ^ (prefixWord ++ tailWord_1062976).sum := by decide
  have hdescent : baseEnd_1062976 < baseStart_1062976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063004 : List Nat := [2, 2, 4, 1, 1, 3, 2, 7]
def baseStart_1063004 : Nat := 118140960795 + 1063004 * 2 ^ 59
def prefixEnd_1063004 : Nat := 4983230072969 + 3 ^ 40 * 1063004 * 2
def baseEnd_1063004 : Nat := 40431999233486238937877

theorem tailTrace_1063004 : CollatzResearch.WordTrace tailWord_1063004 prefixEnd_1063004 40431999233486238937877 := by
  unfold tailWord_1063004
  simp only [CollatzResearch.WordTrace]
  refine ⟨19385470520462764737322033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25847294027283686316429377 19385470520462764737322033)
  ·
    refine ⟨14539102890347073552991525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19385470520462764737322033 14539102890347073552991525)
    ·
      refine ⟨2726081791940076291185911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14539102890347073552991525 2726081791940076291185911)
      ·
        refine ⟨4089122687910114436778867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2726081791940076291185911 4089122687910114436778867)
        ·
          refine ⟨6133684031865171655168301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4089122687910114436778867 6133684031865171655168301)
          ·
            refine ⟨2300131511949439370688113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6133684031865171655168301 2300131511949439370688113)
            ·
              refine ⟨1725098633962079528016085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2300131511949439370688113 1725098633962079528016085)
              ·
                refine ⟨40431999233486238937877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1725098633962079528016085 40431999233486238937877)
                ·
                  rfl

theorem cell22_1063004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 7].length) (baseStart_1063004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1063004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1063004 prefixEnd_1063004 := by exact prefixLift 1063004
  have htrace : WordTrace (prefixWord ++ tailWord_1063004) baseStart_1063004 baseEnd_1063004 := by
    simpa [prefixWord, tailWord_1063004, baseEnd_1063004] using wordTrace_append hprefix tailTrace_1063004
  have hstable : (prefixWord ++ tailWord_1063004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063004).length < 2 ^ (prefixWord ++ tailWord_1063004).sum := by decide
  have hdescent : baseEnd_1063004 < baseStart_1063004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063008 : List Nat := [2, 1, 1, 3, 2, 5, 2, 1, 2, 3]
def baseStart_1063008 : Nat := 118140960795 + 1063008 * 2 ^ 59
def prefixEnd_1063008 : Nat := 4983230072969 + 3 ^ 40 * 1063008 * 2
def baseEnd_1063008 : Nat := 363889362383121473340881

theorem tailTrace_1063008 : CollatzResearch.WordTrace tailWord_1063008 prefixEnd_1063008 363889362383121473340881 := by
  unfold tailWord_1063008
  simp only [CollatzResearch.WordTrace]
  refine ⟨19385543466455519078894839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25847391288607358771859785 19385543466455519078894839)
  ·
    refine ⟨29078315199683278618342259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19385543466455519078894839 29078315199683278618342259)
    ·
      refine ⟨43617472799524917927513389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29078315199683278618342259 43617472799524917927513389)
      ·
        refine ⟨16356552299821844222817521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43617472799524917927513389 16356552299821844222817521)
        ·
          refine ⟨12267414224866383167113141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16356552299821844222817521 12267414224866383167113141)
          ·
            refine ⟨1150070083581223421916857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12267414224866383167113141 1150070083581223421916857)
            ·
              refine ⟨862552562685917566437643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1150070083581223421916857 862552562685917566437643)
              ·
                refine ⟨1293828844028876349656465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 862552562685917566437643 1293828844028876349656465)
                ·
                  refine ⟨970371633021657262242349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1293828844028876349656465 970371633021657262242349)
                  ·
                    refine ⟨363889362383121473340881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 970371633021657262242349 363889362383121473340881)
                    ·
                      rfl

theorem cell22_1063008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 1, 2, 3].length) (baseStart_1063008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1063008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1063008 prefixEnd_1063008 := by exact prefixLift 1063008
  have htrace : WordTrace (prefixWord ++ tailWord_1063008) baseStart_1063008 baseEnd_1063008 := by
    simpa [prefixWord, tailWord_1063008, baseEnd_1063008] using wordTrace_append hprefix tailTrace_1063008
  have hstable : (prefixWord ++ tailWord_1063008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063008).length < 2 ^ (prefixWord ++ tailWord_1063008).sum := by decide
  have hdescent : baseEnd_1063008 < baseStart_1063008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063049 : List Nat := [1, 2, 1, 1, 4, 2, 4, 2, 5]
def baseStart_1063049 : Nat := 118140960795 + 1063049 * 2 ^ 59
def prefixEnd_1063049 : Nat := 4983230072969 + 3 ^ 40 * 1063049 * 2
def baseEnd_1063049 : Nat := 121301132507003677688585

theorem tailTrace_1063049 : CollatzResearch.WordTrace tailWord_1063049 prefixEnd_1063049 121301132507003677688585 := by
  unfold tailWord_1063049
  simp only [CollatzResearch.WordTrace]
  refine ⟨38772582325762502160032201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25848388217175001440021467 38772582325762502160032201)
  ·
    refine ⟨29079436744321876620024151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38772582325762502160032201 29079436744321876620024151)
    ·
      refine ⟨43619155116482814930036227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29079436744321876620024151 43619155116482814930036227)
      ·
        refine ⟨65428732674724222395054341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43619155116482814930036227 65428732674724222395054341)
        ·
          refine ⟨12267887376510791699072689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65428732674724222395054341 12267887376510791699072689)
          ·
            refine ⟨9200915532383093774304517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12267887376510791699072689 9200915532383093774304517)
            ·
              refine ⟨1725171662321830082682097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9200915532383093774304517 1725171662321830082682097)
              ·
                refine ⟨1293878746741372562011573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1725171662321830082682097 1293878746741372562011573)
                ·
                  refine ⟨121301132507003677688585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1293878746741372562011573 121301132507003677688585)
                  ·
                    rfl

theorem cell22_1063049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 2, 5].length) (baseStart_1063049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1063049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1063049 prefixEnd_1063049 := by exact prefixLift 1063049
  have htrace : WordTrace (prefixWord ++ tailWord_1063049) baseStart_1063049 baseEnd_1063049 := by
    simpa [prefixWord, tailWord_1063049, baseEnd_1063049] using wordTrace_append hprefix tailTrace_1063049
  have hstable : (prefixWord ++ tailWord_1063049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063049).length < 2 ^ (prefixWord ++ tailWord_1063049).sum := by decide
  have hdescent : baseEnd_1063049 < baseStart_1063049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063169 : List Nat := [1, 2, 4, 1, 1, 2, 2, 1, 2, 6]
def baseStart_1063169 : Nat := 118140960795 + 1063169 * 2 ^ 59
def prefixEnd_1063169 : Nat := 4983230072969 + 3 ^ 40 * 1063169 * 2
def baseEnd_1063169 : Nat := 363944475973370720065387

theorem tailTrace_1063169 : CollatzResearch.WordTrace tailWord_1063169 prefixEnd_1063169 363944475973370720065387 := by
  unfold tailWord_1063169
  simp only [CollatzResearch.WordTrace]
  refine ⟨38776959085327762654400561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25851306056885175102933707 38776959085327762654400561)
  ·
    refine ⟨29082719313995821990800421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38776959085327762654400561 29082719313995821990800421)
    ·
      refine ⟨5453009871374216623275079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29082719313995821990800421 5453009871374216623275079)
      ·
        refine ⟨8179514807061324934912619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5453009871374216623275079 8179514807061324934912619)
        ·
          refine ⟨12269272210591987402368929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8179514807061324934912619 12269272210591987402368929)
          ·
            refine ⟨9201954157943990551776697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12269272210591987402368929 9201954157943990551776697)
            ·
              refine ⟨6901465618457992913832523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9201954157943990551776697 6901465618457992913832523)
              ·
                refine ⟨10352198427686989370748785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6901465618457992913832523 10352198427686989370748785)
                ·
                  refine ⟨7764148820765242028061589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10352198427686989370748785 7764148820765242028061589)
                  ·
                    refine ⟨363944475973370720065387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7764148820765242028061589 363944475973370720065387)
                    ·
                      rfl

theorem cell22_1063169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_1063169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1063169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1063169 prefixEnd_1063169 := by exact prefixLift 1063169
  have htrace : WordTrace (prefixWord ++ tailWord_1063169) baseStart_1063169 baseEnd_1063169 := by
    simpa [prefixWord, tailWord_1063169, baseEnd_1063169] using wordTrace_append hprefix tailTrace_1063169
  have hstable : (prefixWord ++ tailWord_1063169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063169).length < 2 ^ (prefixWord ++ tailWord_1063169).sum := by decide
  have hdescent : baseEnd_1063169 < baseStart_1063169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063218 : List Nat := [3, 2, 1, 1, 5, 1, 2, 2, 5]
def baseStart_1063218 : Nat := 118140960795 + 1063218 * 2 ^ 59
def prefixEnd_1063218 : Nat := 4983230072969 + 3 ^ 40 * 1063218 * 2
def baseEnd_1063218 : Nat := 121320416558250308530079

theorem tailTrace_1063218 : CollatzResearch.WordTrace tailWord_1063218 prefixEnd_1063218 121320416558250308530079 := by
  unfold tailWord_1063218
  simp only [CollatzResearch.WordTrace]
  refine ⟨9694686565537561005733577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25852497508100162681956205 9694686565537561005733577)
  ·
    refine ⟨7271014924153170754300183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9694686565537561005733577 7271014924153170754300183)
    ·
      refine ⟨10906522386229756131450275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7271014924153170754300183 10906522386229756131450275)
      ·
        refine ⟨16359783579344634197175413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10906522386229756131450275 16359783579344634197175413)
        ·
          refine ⟨1533729710563559455985195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16359783579344634197175413 1533729710563559455985195)
          ·
            refine ⟨2300594565845339183977793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1533729710563559455985195 2300594565845339183977793)
            ·
              refine ⟨1725445924384004387983345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2300594565845339183977793 1725445924384004387983345)
              ·
                refine ⟨1294084443288003290987509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1725445924384004387983345 1294084443288003290987509)
                ·
                  refine ⟨121320416558250308530079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1294084443288003290987509 121320416558250308530079)
                  ·
                    rfl

theorem cell22_1063218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_1063218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1063218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1063218 prefixEnd_1063218 := by exact prefixLift 1063218
  have htrace : WordTrace (prefixWord ++ tailWord_1063218) baseStart_1063218 baseEnd_1063218 := by
    simpa [prefixWord, tailWord_1063218, baseEnd_1063218] using wordTrace_append hprefix tailTrace_1063218
  have hstable : (prefixWord ++ tailWord_1063218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063218).length < 2 ^ (prefixWord ++ tailWord_1063218).sum := by decide
  have hdescent : baseEnd_1063218 < baseStart_1063218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063233 : List Nat := [1, 2, 5, 2, 2, 1, 1, 1, 2, 5]
def baseStart_1063233 : Nat := 118140960795 + 1063233 * 2 ^ 59
def prefixEnd_1063233 : Nat := 4983230072969 + 3 ^ 40 * 1063233 * 2
def baseEnd_1063233 : Nat := 363966384481295886465191

theorem tailTrace_1063233 : CollatzResearch.WordTrace tailWord_1063233 prefixEnd_1063233 363966384481295886465191 := by
  unfold tailWord_1063233
  simp only [CollatzResearch.WordTrace]
  refine ⟨38779293357095901584730353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25852862238063934389820235 38779293357095901584730353)
  ·
    refine ⟨29084470017821926188547765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38779293357095901584730353 29084470017821926188547765)
    ·
      refine ⟨2726669064170805580176353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29084470017821926188547765 2726669064170805580176353)
      ·
        refine ⟨2045001798128104185132265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2726669064170805580176353 2045001798128104185132265)
        ·
          refine ⟨1533751348596078138849199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2045001798128104185132265 1533751348596078138849199)
          ·
            refine ⟨2300627022894117208273799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1533751348596078138849199 2300627022894117208273799)
            ·
              refine ⟨3450940534341175812410699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2300627022894117208273799 3450940534341175812410699)
              ·
                refine ⟨5176410801511763718616049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3450940534341175812410699 5176410801511763718616049)
                ·
                  refine ⟨3882308101133822788962037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5176410801511763718616049 3882308101133822788962037)
                  ·
                    refine ⟨363966384481295886465191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3882308101133822788962037 363966384481295886465191)
                    ·
                      rfl

theorem cell22_1063233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_1063233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1063233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1063233 prefixEnd_1063233 := by exact prefixLift 1063233
  have htrace : WordTrace (prefixWord ++ tailWord_1063233) baseStart_1063233 baseEnd_1063233 := by
    simpa [prefixWord, tailWord_1063233, baseEnd_1063233] using wordTrace_append hprefix tailTrace_1063233
  have hstable : (prefixWord ++ tailWord_1063233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063233).length < 2 ^ (prefixWord ++ tailWord_1063233).sum := by decide
  have hdescent : baseEnd_1063233 < baseStart_1063233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063308 : List Nat := [2, 2, 1, 2, 1, 6, 2, 6]
def baseStart_1063308 : Nat := 118140960795 + 1063308 * 2 ^ 59
def prefixEnd_1063308 : Nat := 4983230072969 + 3 ^ 40 * 1063308 * 2
def baseEnd_1063308 : Nat := 40443562057113410093329

theorem tailTrace_1063308 : CollatzResearch.WordTrace tailWord_1063308 prefixEnd_1063308 40443562057113410093329 := by
  unfold tailWord_1063308
  simp only [CollatzResearch.WordTrace]
  refine ⟨19391014415912094696855289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25854685887882792929140385 19391014415912094696855289)
  ·
    refine ⟨14543260811934071022641467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19391014415912094696855289 14543260811934071022641467)
    ·
      refine ⟨21814891217901106533962201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14543260811934071022641467 21814891217901106533962201)
      ·
        refine ⟨16361168413425829900471651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21814891217901106533962201 16361168413425829900471651)
        ·
          refine ⟨24541752620138744850707477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16361168413425829900471651 24541752620138744850707477)
          ·
            refine ⟨1150394654069003664876913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24541752620138744850707477 1150394654069003664876913)
            ·
              refine ⟨862795990551752748657685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1150394654069003664876913 862795990551752748657685)
              ·
                refine ⟨40443562057113410093329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 862795990551752748657685 40443562057113410093329)
                ·
                  rfl

theorem cell22_1063308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 6].length) (baseStart_1063308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1063308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1063308 prefixEnd_1063308 := by exact prefixLift 1063308
  have htrace : WordTrace (prefixWord ++ tailWord_1063308) baseStart_1063308 baseEnd_1063308 := by
    simpa [prefixWord, tailWord_1063308, baseEnd_1063308] using wordTrace_append hprefix tailTrace_1063308
  have hstable : (prefixWord ++ tailWord_1063308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063308).length < 2 ^ (prefixWord ++ tailWord_1063308).sum := by decide
  have hdescent : baseEnd_1063308 < baseStart_1063308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063353 : List Nat := [1, 2, 1, 4, 3, 2, 1, 3, 5]
def baseStart_1063353 : Nat := 118140960795 + 1063353 * 2 ^ 59
def prefixEnd_1063353 : Nat := 4983230072969 + 3 ^ 40 * 1063353 * 2
def baseEnd_1063353 : Nat := 121335820977885191154941

theorem tailTrace_1063353 : CollatzResearch.WordTrace tailWord_1063353 prefixEnd_1063353 121335820977885191154941 := by
  unfold tailWord_1063353
  simp only [CollatzResearch.WordTrace]
  refine ⟨38783670116661162079098713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25855780077774108052732475 38783670116661162079098713)
  ·
    refine ⟨29087752587495871559324035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38783670116661162079098713 29087752587495871559324035)
    ·
      refine ⟨43631628881243807338986053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29087752587495871559324035 43631628881243807338986053)
      ·
        refine ⟨8180930415233213876059885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43631628881243807338986053 8180930415233213876059885)
        ·
          refine ⟨3067848905712455203522457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8180930415233213876059885 3067848905712455203522457)
          ·
            refine ⟨2300886679284341402641843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3067848905712455203522457 2300886679284341402641843)
            ·
              refine ⟨3451330018926512103962765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2300886679284341402641843 3451330018926512103962765)
              ·
                refine ⟨1294248757097442038986037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3451330018926512103962765 1294248757097442038986037)
                ·
                  refine ⟨121335820977885191154941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1294248757097442038986037 121335820977885191154941)
                  ·
                    rfl

theorem cell22_1063353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 3, 5].length) (baseStart_1063353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1063353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1063353 prefixEnd_1063353 := by exact prefixLift 1063353
  have htrace : WordTrace (prefixWord ++ tailWord_1063353) baseStart_1063353 baseEnd_1063353 := by
    simpa [prefixWord, tailWord_1063353, baseEnd_1063353] using wordTrace_append hprefix tailTrace_1063353
  have hstable : (prefixWord ++ tailWord_1063353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063353).length < 2 ^ (prefixWord ++ tailWord_1063353).sum := by decide
  have hdescent : baseEnd_1063353 < baseStart_1063353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063411 : List Nat := [1, 1, 1, 2, 2, 2, 4, 2, 1, 6]
def baseStart_1063411 : Nat := 118140960795 + 1063411 * 2 ^ 59
def prefixEnd_1063411 : Nat := 4983230072969 + 3 ^ 40 * 1063411 * 2
def baseEnd_1063411 : Nat := 364027317518962755514645

theorem tailTrace_1063411 : CollatzResearch.WordTrace tailWord_1063411 prefixEnd_1063411 364027317518962755514645 := by
  unfold tailWord_1063411
  simp only [CollatzResearch.WordTrace]
  refine ⟨38785785550451037984710087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25857190366967358656473391 38785785550451037984710087)
  ·
    refine ⟨58178678325676556977065131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38785785550451037984710087 58178678325676556977065131)
    ·
      refine ⟨87268017488514835465597697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58178678325676556977065131 87268017488514835465597697)
      ·
        refine ⟨65451013116386126599198273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87268017488514835465597697 65451013116386126599198273)
        ·
          refine ⟨49088259837289594949398705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65451013116386126599198273 49088259837289594949398705)
          ·
            refine ⟨36816194877967196212049029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49088259837289594949398705 36816194877967196212049029)
            ·
              refine ⟨6903036539618849289759193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36816194877967196212049029 6903036539618849289759193)
              ·
                refine ⟨5177277404714136967319395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6903036539618849289759193 5177277404714136967319395)
                ·
                  refine ⟨7765916107071205450979093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5177277404714136967319395 7765916107071205450979093)
                  ·
                    refine ⟨364027317518962755514645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7765916107071205450979093 364027317518962755514645)
                    ·
                      rfl

theorem cell22_1063411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 6].length) (baseStart_1063411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1063411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1063411 prefixEnd_1063411 := by exact prefixLift 1063411
  have htrace : WordTrace (prefixWord ++ tailWord_1063411) baseStart_1063411 baseEnd_1063411 := by
    simpa [prefixWord, tailWord_1063411, baseEnd_1063411] using wordTrace_append hprefix tailTrace_1063411
  have hstable : (prefixWord ++ tailWord_1063411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063411).length < 2 ^ (prefixWord ++ tailWord_1063411).sum := by decide
  have hdescent : baseEnd_1063411 < baseStart_1063411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063447 : List Nat := [1, 1, 3, 6, 1, 1, 1, 1, 4, 3]
def baseStart_1063447 : Nat := 118140960795 + 1063447 * 2 ^ 59
def prefixEnd_1063447 : Nat := 4983230072969 + 3 ^ 40 * 1063447 * 2
def baseEnd_1063447 : Nat := 364039641054670661614535

theorem tailTrace_1063447 : CollatzResearch.WordTrace tailWord_1063447 prefixEnd_1063447 364039641054670661614535 := by
  unfold tailWord_1063447
  simp only [CollatzResearch.WordTrace]
  refine ⟨38787098578320616133020595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25858065718880410755347063 38787098578320616133020595)
  ·
    refine ⟨58180647867480924199530893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38787098578320616133020595 58180647867480924199530893)
    ·
      refine ⟨21817742950305346574824085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58180647867480924199530893 21817742950305346574824085)
      ·
        refine ⟨1022706700795563120694879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 21817742950305346574824085 1022706700795563120694879)
        ·
          refine ⟨1534060051193344681042319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1022706700795563120694879 1534060051193344681042319)
          ·
            refine ⟨2301090076790017021563479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1534060051193344681042319 2301090076790017021563479)
            ·
              refine ⟨3451635115185025532345219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2301090076790017021563479 3451635115185025532345219)
              ·
                refine ⟨5177452672777538298517829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3451635115185025532345219 5177452672777538298517829)
                ·
                  refine ⟨970772376145788430972093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5177452672777538298517829 970772376145788430972093)
                  ·
                    refine ⟨364039641054670661614535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 970772376145788430972093 364039641054670661614535)
                    ·
                      rfl

theorem cell22_1063447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 4, 3].length) (baseStart_1063447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1063447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1063447 prefixEnd_1063447 := by exact prefixLift 1063447
  have htrace : WordTrace (prefixWord ++ tailWord_1063447) baseStart_1063447 baseEnd_1063447 := by
    simpa [prefixWord, tailWord_1063447, baseEnd_1063447] using wordTrace_append hprefix tailTrace_1063447
  have hstable : (prefixWord ++ tailWord_1063447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063447).length < 2 ^ (prefixWord ++ tailWord_1063447).sum := by decide
  have hdescent : baseEnd_1063447 < baseStart_1063447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063464 : List Nat := [2, 1, 5, 2, 1, 2, 3, 1, 2, 3]
def baseStart_1063464 : Nat := 118140960795 + 1063464 * 2 ^ 59
def prefixEnd_1063464 : Nat := 4983230072969 + 3 ^ 40 * 1063464 * 2
def baseEnd_1063464 : Nat := 364045460502088283939483

theorem tailTrace_1063464 : CollatzResearch.WordTrace tailWord_1063464 prefixEnd_1063464 364045460502088283939483 := by
  unfold tailWord_1063464
  simp only [CollatzResearch.WordTrace]
  refine ⟨19393859309629514018194723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25858479079506018690926297 19393859309629514018194723)
  ·
    refine ⟨29090788964444271027292085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19393859309629514018194723 29090788964444271027292085)
    ·
      refine ⟨2727261465416650408808633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29090788964444271027292085 2727261465416650408808633)
      ·
        refine ⟨2045446099062487806606475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2727261465416650408808633 2045446099062487806606475)
        ·
          refine ⟨3068169148593731709909713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2045446099062487806606475 3068169148593731709909713)
          ·
            refine ⟨2301126861445298782432285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3068169148593731709909713 2301126861445298782432285)
            ·
              refine ⟨862922573041987043412107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2301126861445298782432285 862922573041987043412107)
              ·
                refine ⟨1294383859562980565118161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 862922573041987043412107 1294383859562980565118161)
                ·
                  refine ⟨970787894672235423838621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1294383859562980565118161 970787894672235423838621)
                  ·
                    refine ⟨364045460502088283939483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 970787894672235423838621 364045460502088283939483)
                    ·
                      rfl

theorem cell22_1063464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_1063464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1063464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1063464 prefixEnd_1063464 := by exact prefixLift 1063464
  have htrace : WordTrace (prefixWord ++ tailWord_1063464) baseStart_1063464 baseEnd_1063464 := by
    simpa [prefixWord, tailWord_1063464, baseEnd_1063464] using wordTrace_append hprefix tailTrace_1063464
  have hstable : (prefixWord ++ tailWord_1063464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063464).length < 2 ^ (prefixWord ++ tailWord_1063464).sum := by decide
  have hdescent : baseEnd_1063464 < baseStart_1063464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063535 : List Nat := [1, 1, 2, 1, 3, 2, 5, 2, 1, 4]
def baseStart_1063535 : Nat := 118140960795 + 1063535 * 2 ^ 59
def prefixEnd_1063535 : Nat := 4983230072969 + 3 ^ 40 * 1063535 * 2
def baseEnd_1063535 : Nat := 364069765253067765414265

theorem tailTrace_1063535 : CollatzResearch.WordTrace tailWord_1063535 prefixEnd_1063535 364069765253067765414265 := by
  unfold tailWord_1063535
  simp only [CollatzResearch.WordTrace]
  refine ⟨38790308202001807162224059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25860205468001204774816039 38790308202001807162224059)
  ·
    refine ⟨58185462303002710743336089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38790308202001807162224059 58185462303002710743336089)
    ·
      refine ⟨43639096727252033057502067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58185462303002710743336089 43639096727252033057502067)
      ·
        refine ⟨65458645090878049586253101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43639096727252033057502067 65458645090878049586253101)
        ·
          refine ⟨24546991909079268594844913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65458645090878049586253101 24546991909079268594844913)
          ·
            refine ⟨18410243931809451446133685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24546991909079268594844913 18410243931809451446133685)
            ·
              refine ⟨1725960368607136073075033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18410243931809451446133685 1725960368607136073075033)
              ·
                refine ⟨1294470276455352054806275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1725960368607136073075033 1294470276455352054806275)
                ·
                  refine ⟨1941705414683028082209413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1294470276455352054806275 1941705414683028082209413)
                  ·
                    refine ⟨364069765253067765414265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1941705414683028082209413 364069765253067765414265)
                    ·
                      rfl

theorem cell22_1063535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 2, 1, 4].length) (baseStart_1063535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1063535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1063535 prefixEnd_1063535 := by exact prefixLift 1063535
  have htrace : WordTrace (prefixWord ++ tailWord_1063535) baseStart_1063535 baseEnd_1063535 := by
    simpa [prefixWord, tailWord_1063535, baseEnd_1063535] using wordTrace_append hprefix tailTrace_1063535
  have hstable : (prefixWord ++ tailWord_1063535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063535).length < 2 ^ (prefixWord ++ tailWord_1063535).sum := by decide
  have hdescent : baseEnd_1063535 < baseStart_1063535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063548 : List Nat := [2, 2, 2, 1, 1, 2, 3, 1, 3, 5]
def baseStart_1063548 : Nat := 118140960795 + 1063548 * 2 ^ 59
def prefixEnd_1063548 : Nat := 4983230072969 + 3 ^ 40 * 1063548 * 2
def baseEnd_1063548 : Nat := 364074215418740064839225

theorem tailTrace_1063548 : CollatzResearch.WordTrace tailWord_1063548 prefixEnd_1063548 364074215418740064839225 := by
  unfold tailWord_1063548
  simp only [CollatzResearch.WordTrace]
  refine ⟨19395391175477355191223649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25860521567303140254964865 19395391175477355191223649)
  ·
    refine ⟨14546543381608016393417737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19395391175477355191223649 14546543381608016393417737)
    ·
      refine ⟨10909907536206012295063303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14546543381608016393417737 10909907536206012295063303)
      ·
        refine ⟨16364861304309018442594955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10909907536206012295063303 16364861304309018442594955)
        ·
          refine ⟨24547291956463527663892433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16364861304309018442594955 24547291956463527663892433)
          ·
            refine ⟨18410468967347645747919325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24547291956463527663892433 18410468967347645747919325)
            ·
              refine ⟨6903925862755367155469747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18410468967347645747919325 6903925862755367155469747)
              ·
                refine ⟨10355888794133050733204621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6903925862755367155469747 10355888794133050733204621)
                ·
                  refine ⟨3883458297799894024951733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10355888794133050733204621 3883458297799894024951733)
                  ·
                    refine ⟨364074215418740064839225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3883458297799894024951733 364074215418740064839225)
                    ·
                      rfl

theorem cell22_1063548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_1063548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1063548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1063548 prefixEnd_1063548 := by exact prefixLift 1063548
  have htrace : WordTrace (prefixWord ++ tailWord_1063548) baseStart_1063548 baseEnd_1063548 := by
    simpa [prefixWord, tailWord_1063548, baseEnd_1063548] using wordTrace_append hprefix tailTrace_1063548
  have hstable : (prefixWord ++ tailWord_1063548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063548).length < 2 ^ (prefixWord ++ tailWord_1063548).sum := by decide
  have hdescent : baseEnd_1063548 < baseStart_1063548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063552 : List Nat := [2, 1, 1, 2, 1, 6, 3, 1, 1, 4]
def baseStart_1063552 : Nat := 118140960795 + 1063552 * 2 ^ 59
def prefixEnd_1063552 : Nat := 4983230072969 + 3 ^ 40 * 1063552 * 2
def baseEnd_1063552 : Nat := 364075584700485387739213

theorem tailTrace_1063552 : CollatzResearch.WordTrace tailWord_1063552 prefixEnd_1063552 364075584700485387739213 := by
  unfold tailWord_1063552
  simp only [CollatzResearch.WordTrace]
  refine ⟨19395464121470109532796455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25860618828626812710395273 19395464121470109532796455)
  ·
    refine ⟨29093196182205164299194683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19395464121470109532796455 29093196182205164299194683)
    ·
      refine ⟨43639794273307746448792025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29093196182205164299194683 43639794273307746448792025)
      ·
        refine ⟨32729845704980809836594019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43639794273307746448792025 32729845704980809836594019)
        ·
          refine ⟨49094768557471214754891029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32729845704980809836594019 49094768557471214754891029)
          ·
            refine ⟨2301317276131463191635517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 49094768557471214754891029 2301317276131463191635517)
            ·
              refine ⟨862993978549298696863319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2301317276131463191635517 862993978549298696863319)
              ·
                refine ⟨1294490967823948045294979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 862993978549298696863319 1294490967823948045294979)
                ·
                  refine ⟨1941736451735922067942469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1294490967823948045294979 1941736451735922067942469)
                  ·
                    refine ⟨364075584700485387739213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1941736451735922067942469 364075584700485387739213)
                    ·
                      rfl

theorem cell22_1063552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 1, 1, 4].length) (baseStart_1063552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1063552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1063552 prefixEnd_1063552 := by exact prefixLift 1063552
  have htrace : WordTrace (prefixWord ++ tailWord_1063552) baseStart_1063552 baseEnd_1063552 := by
    simpa [prefixWord, tailWord_1063552, baseEnd_1063552] using wordTrace_append hprefix tailTrace_1063552
  have hstable : (prefixWord ++ tailWord_1063552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063552).length < 2 ^ (prefixWord ++ tailWord_1063552).sum := by decide
  have hdescent : baseEnd_1063552 < baseStart_1063552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063563 : List Nat := [1, 1, 1, 1, 4, 1, 2, 3, 4, 4]
def baseStart_1063563 : Nat := 118140960795 + 1063563 * 2 ^ 59
def prefixEnd_1063563 : Nat := 4983230072969 + 3 ^ 40 * 1063563 * 2
def baseEnd_1063563 : Nat := 364079350225285025714179

theorem tailTrace_1063563 : CollatzResearch.WordTrace tailWord_1063563 prefixEnd_1063563 364079350225285025714179 := by
  unfold tailWord_1063563
  simp only [CollatzResearch.WordTrace]
  refine ⟨38791329445900367944243343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25860886297266911962828895 38791329445900367944243343)
  ·
    refine ⟨58186994168850551916365015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38791329445900367944243343 58186994168850551916365015)
    ·
      refine ⟨87280491253275827874547523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58186994168850551916365015 87280491253275827874547523)
      ·
        refine ⟨130920736879913741811821285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87280491253275827874547523 130920736879913741811821285)
        ·
          refine ⟨24547638164983826589716491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 130920736879913741811821285 24547638164983826589716491)
          ·
            refine ⟨36821457247475739884574737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24547638164983826589716491 36821457247475739884574737)
            ·
              refine ⟨27616092935606804913431053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36821457247475739884574737 27616092935606804913431053)
              ·
                refine ⟨10356034850852551842536645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27616092935606804913431053 10356034850852551842536645)
                ·
                  refine ⟨1941756534534853470475621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10356034850852551842536645 1941756534534853470475621)
                  ·
                    refine ⟨364079350225285025714179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1941756534534853470475621 364079350225285025714179)
                    ·
                      rfl

theorem cell22_1063563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 4, 4].length) (baseStart_1063563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1063563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1063563 prefixEnd_1063563 := by exact prefixLift 1063563
  have htrace : WordTrace (prefixWord ++ tailWord_1063563) baseStart_1063563 baseEnd_1063563 := by
    simpa [prefixWord, tailWord_1063563, baseEnd_1063563] using wordTrace_append hprefix tailTrace_1063563
  have hstable : (prefixWord ++ tailWord_1063563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063563).length < 2 ^ (prefixWord ++ tailWord_1063563).sum := by decide
  have hdescent : baseEnd_1063563 < baseStart_1063563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063582 : List Nat := [4, 3, 1, 1, 1, 1, 4, 1, 1, 5]
def baseStart_1063582 : Nat := 118140960795 + 1063582 * 2 ^ 59
def prefixEnd_1063582 : Nat := 4983230072969 + 3 ^ 40 * 1063582 * 2
def baseEnd_1063582 : Nat := 364085854313575309489121

theorem tailTrace_1063582 : CollatzResearch.WordTrace tailWord_1063582 prefixEnd_1063582 364085854313575309489121 := by
  unfold tailWord_1063582
  simp only [CollatzResearch.WordTrace]
  refine ⟨4849002804103941773648125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25861348288554356126123333 4849002804103941773648125)
  ·
    refine ⟨1818376051538978165118047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4849002804103941773648125 1818376051538978165118047)
    ·
      refine ⟨2727564077308467247677071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1818376051538978165118047 2727564077308467247677071)
      ·
        refine ⟨4091346115962700871515607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2727564077308467247677071 4091346115962700871515607)
        ·
          refine ⟨6137019173944051307273411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4091346115962700871515607 6137019173944051307273411)
          ·
            refine ⟨9205528760916076960910117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6137019173944051307273411 9205528760916076960910117)
            ·
              refine ⟨1726036642671764430170647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9205528760916076960910117 1726036642671764430170647)
              ·
                refine ⟨2589054964007646645255971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1726036642671764430170647 2589054964007646645255971)
                ·
                  refine ⟨3883582446011469967883957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2589054964007646645255971 3883582446011469967883957)
                  ·
                    refine ⟨364085854313575309489121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3883582446011469967883957 364085854313575309489121)
                    ·
                      rfl

theorem cell22_1063582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_1063582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1063582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1063582 prefixEnd_1063582 := by exact prefixLift 1063582
  have htrace : WordTrace (prefixWord ++ tailWord_1063582) baseStart_1063582 baseEnd_1063582 := by
    simpa [prefixWord, tailWord_1063582, baseEnd_1063582] using wordTrace_append hprefix tailTrace_1063582
  have hstable : (prefixWord ++ tailWord_1063582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063582).length < 2 ^ (prefixWord ++ tailWord_1063582).sum := by decide
  have hdescent : baseEnd_1063582 < baseStart_1063582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063597 : List Nat := [1, 5, 2, 1, 1, 2, 3, 1, 2, 4]
def baseStart_1063597 : Nat := 118140960795 + 1063597 * 2 ^ 59
def prefixEnd_1063597 : Nat := 4983230072969 + 3 ^ 40 * 1063597 * 2
def baseEnd_1063597 : Nat := 364090989120120270364075

theorem tailTrace_1063597 : CollatzResearch.WordTrace tailWord_1063597 prefixEnd_1063597 364090989120120270364075 := by
  unfold tailWord_1063597
  simp only [CollatzResearch.WordTrace]
  refine ⟨38792569527777191750981045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25861713018518127833987363 38792569527777191750981045)
  ·
    refine ⟨3636803393229111726654473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38792569527777191750981045 3636803393229111726654473)
    ·
      refine ⟨2727602544921833794990855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3636803393229111726654473 2727602544921833794990855)
      ·
        refine ⟨4091403817382750692486283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2727602544921833794990855 4091403817382750692486283)
        ·
          refine ⟨6137105726074126038729425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4091403817382750692486283 6137105726074126038729425)
          ·
            refine ⟨4602829294555594529047069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6137105726074126038729425 4602829294555594529047069)
            ·
              refine ⟨1726060985458347948392651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4602829294555594529047069 1726060985458347948392651)
              ·
                refine ⟨2589091478187521922588977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1726060985458347948392651 2589091478187521922588977)
                ·
                  refine ⟨1941818608640641441941733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2589091478187521922588977 1941818608640641441941733)
                  ·
                    refine ⟨364090989120120270364075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1941818608640641441941733 364090989120120270364075)
                    ·
                      rfl

theorem cell22_1063597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_1063597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1063597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1063597 prefixEnd_1063597 := by exact prefixLift 1063597
  have htrace : WordTrace (prefixWord ++ tailWord_1063597) baseStart_1063597 baseEnd_1063597 := by
    simpa [prefixWord, tailWord_1063597, baseEnd_1063597] using wordTrace_append hprefix tailTrace_1063597
  have hstable : (prefixWord ++ tailWord_1063597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063597).length < 2 ^ (prefixWord ++ tailWord_1063597).sum := by decide
  have hdescent : baseEnd_1063597 < baseStart_1063597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063610 : List Nat := [3, 1, 1, 1, 2, 3, 1, 2, 5, 3]
def baseStart_1063610 : Nat := 118140960795 + 1063610 * 2 ^ 59
def prefixEnd_1063610 : Nat := 4983230072969 + 3 ^ 40 * 1063610 * 2
def baseEnd_1063610 : Nat := 364095439285792569789035

theorem tailTrace_1063610 : CollatzResearch.WordTrace tailWord_1063610 prefixEnd_1063610 364095439285792569789035 := by
  unfold tailWord_1063610
  simp only [CollatzResearch.WordTrace]
  refine ⟨9698260919182523742801071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25862029117820063314136189 9698260919182523742801071)
  ·
    refine ⟨14547391378773785614201607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9698260919182523742801071 14547391378773785614201607)
    ·
      refine ⟨21821087068160678421302411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14547391378773785614201607 21821087068160678421302411)
      ·
        refine ⟨32731630602241017631953617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21821087068160678421302411 32731630602241017631953617)
        ·
          refine ⟨24548722951680763223965213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32731630602241017631953617 24548722951680763223965213)
          ·
            refine ⟨9205771106880286208986955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24548722951680763223965213 9205771106880286208986955)
            ·
              refine ⟨13808656660320429313480433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9205771106880286208986955 13808656660320429313480433)
              ·
                refine ⟨10356492495240321985110325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13808656660320429313480433 10356492495240321985110325)
                ·
                  refine ⟨970921171428780186104093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10356492495240321985110325 970921171428780186104093)
                  ·
                    refine ⟨364095439285792569789035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 970921171428780186104093 364095439285792569789035)
                    ·
                      rfl

theorem cell22_1063610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 5, 3].length) (baseStart_1063610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1063610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1063610 prefixEnd_1063610 := by exact prefixLift 1063610
  have htrace : WordTrace (prefixWord ++ tailWord_1063610) baseStart_1063610 baseEnd_1063610 := by
    simpa [prefixWord, tailWord_1063610, baseEnd_1063610] using wordTrace_append hprefix tailTrace_1063610
  have hstable : (prefixWord ++ tailWord_1063610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063610).length < 2 ^ (prefixWord ++ tailWord_1063610).sum := by decide
  have hdescent : baseEnd_1063610 < baseStart_1063610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063644 : List Nat := [2, 2, 5, 1, 1, 1, 2, 2, 3, 3]
def baseStart_1063644 : Nat := 118140960795 + 1063644 * 2 ^ 59
def prefixEnd_1063644 : Nat := 4983230072969 + 3 ^ 40 * 1063644 * 2
def baseEnd_1063644 : Nat := 364107078180627814438931

theorem tailTrace_1063644 : CollatzResearch.WordTrace tailWord_1063644 prefixEnd_1063644 364107078180627814438931 := by
  unfold tailWord_1063644
  simp only [CollatzResearch.WordTrace]
  refine ⟨19397141879303459388970993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25862855839071279185294657 19397141879303459388970993)
  ·
    refine ⟨14547856409477594541728245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19397141879303459388970993 14547856409477594541728245)
    ·
      refine ⟨1363861538388524488287023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14547856409477594541728245 1363861538388524488287023)
      ·
        refine ⟨2045792307582786732430535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1363861538388524488287023 2045792307582786732430535)
        ·
          refine ⟨3068688461374180098645803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2045792307582786732430535 3068688461374180098645803)
          ·
            refine ⟨4603032692061270147968705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3068688461374180098645803 4603032692061270147968705)
            ·
              refine ⟨3452274519045952610976529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4603032692061270147968705 3452274519045952610976529)
              ·
                refine ⟨2589205889284464458232397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3452274519045952610976529 2589205889284464458232397)
                ·
                  refine ⟨970952208481674171837149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2589205889284464458232397 970952208481674171837149)
                  ·
                    refine ⟨364107078180627814438931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 970952208481674171837149 364107078180627814438931)
                    ·
                      rfl

theorem cell22_1063644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_1063644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1063644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1063644 prefixEnd_1063644 := by exact prefixLift 1063644
  have htrace : WordTrace (prefixWord ++ tailWord_1063644) baseStart_1063644 baseEnd_1063644 := by
    simpa [prefixWord, tailWord_1063644, baseEnd_1063644] using wordTrace_append hprefix tailTrace_1063644
  have hstable : (prefixWord ++ tailWord_1063644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063644).length < 2 ^ (prefixWord ++ tailWord_1063644).sum := by decide
  have hdescent : baseEnd_1063644 < baseStart_1063644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063678 : List Nat := [4, 2, 2, 1, 2, 2, 3, 2, 1, 3]
def baseStart_1063678 : Nat := 118140960795 + 1063678 * 2 ^ 59
def prefixEnd_1063678 : Nat := 4983230072969 + 3 ^ 40 * 1063678 * 2
def baseEnd_1063678 : Nat := 364118717075463059088827

theorem tailTrace_1063678 : CollatzResearch.WordTrace tailWord_1063678 prefixEnd_1063678 364118717075463059088827 := by
  unfold tailWord_1063678
  simp only [CollatzResearch.WordTrace]
  refine ⟨4849440480060467823084961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25863682560322495056453125 4849440480060467823084961)
  ·
    refine ⟨3637080360045350867313721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4849440480060467823084961 3637080360045350867313721)
    ·
      refine ⟨2727810270034013150485291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3637080360045350867313721 2727810270034013150485291)
      ·
        refine ⟨4091715405051019725727937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2727810270034013150485291 4091715405051019725727937)
        ·
          refine ⟨3068786553788264794295953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4091715405051019725727937 3068786553788264794295953)
          ·
            refine ⟨2301589915341198595721965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3068786553788264794295953 2301589915341198595721965)
            ·
              refine ⟨863096218252949473395737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2301589915341198595721965 863096218252949473395737)
              ·
                refine ⟨647322163689712105046803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 863096218252949473395737 647322163689712105046803)
                ·
                  refine ⟨970983245534568157570205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 647322163689712105046803 970983245534568157570205)
                  ·
                    refine ⟨364118717075463059088827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 970983245534568157570205 364118717075463059088827)
                    ·
                      rfl

theorem cell22_1063678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_1063678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1063678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1063678 prefixEnd_1063678 := by exact prefixLift 1063678
  have htrace : WordTrace (prefixWord ++ tailWord_1063678) baseStart_1063678 baseEnd_1063678 := by
    simpa [prefixWord, tailWord_1063678, baseEnd_1063678] using wordTrace_append hprefix tailTrace_1063678
  have hstable : (prefixWord ++ tailWord_1063678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063678).length < 2 ^ (prefixWord ++ tailWord_1063678).sum := by decide
  have hdescent : baseEnd_1063678 < baseStart_1063678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063764 : List Nat := [2, 4, 1, 1, 4, 1, 3, 6]
def baseStart_1063764 : Nat := 118140960795 + 1063764 * 2 ^ 59
def prefixEnd_1063764 : Nat := 4983230072969 + 3 ^ 40 * 1063764 * 2
def baseEnd_1063764 : Nat := 40460906292554166826507

theorem tailTrace_1063764 : CollatzResearch.WordTrace tailWord_1063764 prefixEnd_1063764 40460906292554166826507 := by
  unfold tailWord_1063764
  simp only [CollatzResearch.WordTrace]
  refine ⟨19399330259086089636155173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25865773678781452848206897 19399330259086089636155173)
  ·
    refine ⟨3637374423578641806779095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19399330259086089636155173 3637374423578641806779095)
    ·
      refine ⟨5456061635367962710168643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3637374423578641806779095 5456061635367962710168643)
      ·
        refine ⟨8184092453051944065252965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5456061635367962710168643 8184092453051944065252965)
        ·
          refine ⟨1534517334947239512234931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8184092453051944065252965 1534517334947239512234931)
          ·
            refine ⟨2301776002420859268352397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1534517334947239512234931 2301776002420859268352397)
            ·
              refine ⟨863166000907822225632149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2301776002420859268352397 863166000907822225632149)
              ·
                refine ⟨40460906292554166826507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 863166000907822225632149 40460906292554166826507)
                ·
                  rfl

theorem cell22_1063764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 6].length) (baseStart_1063764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1063764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1063764 prefixEnd_1063764 := by exact prefixLift 1063764
  have htrace : WordTrace (prefixWord ++ tailWord_1063764) baseStart_1063764 baseEnd_1063764 := by
    simpa [prefixWord, tailWord_1063764, baseEnd_1063764] using wordTrace_append hprefix tailTrace_1063764
  have hstable : (prefixWord ++ tailWord_1063764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063764).length < 2 ^ (prefixWord ++ tailWord_1063764).sum := by decide
  have hdescent : baseEnd_1063764 < baseStart_1063764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063775 : List Nat := [1, 1, 2, 3, 1, 3, 2, 2, 7]
def baseStart_1063775 : Nat := 118140960795 + 1063775 * 2 ^ 59
def prefixEnd_1063775 : Nat := 4983230072969 + 3 ^ 40 * 1063775 * 2
def baseEnd_1063775 : Nat := 121383974052595713137843

theorem tailTrace_1063775 : CollatzResearch.WordTrace tailWord_1063775 prefixEnd_1063775 121383974052595713137843 := by
  unfold tailWord_1063775
  simp only [CollatzResearch.WordTrace]
  refine ⟨38799061721132328150960779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25866041147421552100640519 38799061721132328150960779)
  ·
    refine ⟨58198592581698492226441169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38799061721132328150960779 58198592581698492226441169)
    ·
      refine ⟨43648944436273869169830877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58198592581698492226441169 43648944436273869169830877)
      ·
        refine ⟨16368354163602700938686579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43648944436273869169830877 16368354163602700938686579)
        ·
          refine ⟨24552531245404051408029869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16368354163602700938686579 24552531245404051408029869)
          ·
            refine ⟨9207199217026519278011201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24552531245404051408029869 9207199217026519278011201)
            ·
              refine ⟨6905399412769889458508401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9207199217026519278011201 6905399412769889458508401)
              ·
                refine ⟨5179049559577417093881301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6905399412769889458508401 5179049559577417093881301)
                ·
                  refine ⟨121383974052595713137843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5179049559577417093881301 121383974052595713137843)
                  ·
                    rfl

theorem cell22_1063775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 7].length) (baseStart_1063775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1063775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1063775 prefixEnd_1063775 := by exact prefixLift 1063775
  have htrace : WordTrace (prefixWord ++ tailWord_1063775) baseStart_1063775 baseEnd_1063775 := by
    simpa [prefixWord, tailWord_1063775, baseEnd_1063775] using wordTrace_append hprefix tailTrace_1063775
  have hstable : (prefixWord ++ tailWord_1063775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063775).length < 2 ^ (prefixWord ++ tailWord_1063775).sum := by decide
  have hdescent : baseEnd_1063775 < baseStart_1063775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063792 : List Nat := [2, 1, 1, 1, 4, 1, 5, 2, 5]
def baseStart_1063792 : Nat := 118140960795 + 1063792 * 2 ^ 59
def prefixEnd_1063792 : Nat := 4983230072969 + 3 ^ 40 * 1063792 * 2
def baseEnd_1063792 : Nat := 121385913868401587246159

theorem tailTrace_1063792 : CollatzResearch.WordTrace tailWord_1063792 prefixEnd_1063792 121385913868401587246159 := by
  unfold tailWord_1063792
  simp only [CollatzResearch.WordTrace]
  refine ⟨19399840881035370027164815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25866454508047160036219753 19399840881035370027164815)
  ·
    refine ⟨29099761321553055040747223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19399840881035370027164815 29099761321553055040747223)
    ·
      refine ⟨43649641982329582561120835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29099761321553055040747223 43649641982329582561120835)
      ·
        refine ⟨65474462973494373841681253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43649641982329582561120835 65474462973494373841681253)
        ·
          refine ⟨12276461807530195095315235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65474462973494373841681253 12276461807530195095315235)
          ·
            refine ⟨18414692711295292642972853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12276461807530195095315235 18414692711295292642972853)
            ·
              refine ⟨1726377441683933685278705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18414692711295292642972853 1726377441683933685278705)
              ·
                refine ⟨1294783081262950263959029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1726377441683933685278705 1294783081262950263959029)
                ·
                  refine ⟨121385913868401587246159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1294783081262950263959029 121385913868401587246159)
                  ·
                    rfl

theorem cell22_1063792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 2, 5].length) (baseStart_1063792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1063792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1063792 prefixEnd_1063792 := by exact prefixLift 1063792
  have htrace : WordTrace (prefixWord ++ tailWord_1063792) baseStart_1063792 baseEnd_1063792 := by
    simpa [prefixWord, tailWord_1063792, baseEnd_1063792] using wordTrace_append hprefix tailTrace_1063792
  have hstable : (prefixWord ++ tailWord_1063792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063792).length < 2 ^ (prefixWord ++ tailWord_1063792).sum := by decide
  have hdescent : baseEnd_1063792 < baseStart_1063792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063839 : List Nat := [1, 1, 2, 5, 2, 1, 2, 3, 1, 4]
def baseStart_1063839 : Nat := 118140960795 + 1063839 * 2 ^ 59
def prefixEnd_1063839 : Nat := 4983230072969 + 3 ^ 40 * 1063839 * 2
def baseEnd_1063839 : Nat := 364173830665712305813333

theorem tailTrace_1063839 : CollatzResearch.WordTrace tailWord_1063839 prefixEnd_1063839 364173830665712305813333 := by
  unfold tailWord_1063839
  simp only [CollatzResearch.WordTrace]
  refine ⟨38801395992900467081290571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25867597328600311387527047 38801395992900467081290571)
  ·
    refine ⟨58202093989350700621935857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38801395992900467081290571 58202093989350700621935857)
    ·
      refine ⟨43651570492013025466451893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58202093989350700621935857 43651570492013025466451893)
      ·
        refine ⟨4092334733626221137479865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43651570492013025466451893 4092334733626221137479865)
        ·
          refine ⟨3069251050219665853109899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4092334733626221137479865 3069251050219665853109899)
          ·
            refine ⟨4603876575329498779664849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3069251050219665853109899 4603876575329498779664849)
            ·
              refine ⟨3452907431497124084748637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4603876575329498779664849 3452907431497124084748637)
              ·
                refine ⟨1294840286811421531780739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3452907431497124084748637 1294840286811421531780739)
                ·
                  refine ⟨1942260430217132297671109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1294840286811421531780739 1942260430217132297671109)
                  ·
                    refine ⟨364173830665712305813333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1942260430217132297671109 364173830665712305813333)
                    ·
                      rfl

theorem cell22_1063839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 3, 1, 4].length) (baseStart_1063839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1063839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1063839 prefixEnd_1063839 := by exact prefixLift 1063839
  have htrace : WordTrace (prefixWord ++ tailWord_1063839) baseStart_1063839 baseEnd_1063839 := by
    simpa [prefixWord, tailWord_1063839, baseEnd_1063839] using wordTrace_append hprefix tailTrace_1063839
  have hstable : (prefixWord ++ tailWord_1063839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063839).length < 2 ^ (prefixWord ++ tailWord_1063839).sum := by decide
  have hdescent : baseEnd_1063839 < baseStart_1063839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063884 : List Nat := [2, 2, 1, 4, 1, 1, 4, 1, 2, 4]
def baseStart_1063884 : Nat := 118140960795 + 1063884 * 2 ^ 59
def prefixEnd_1063884 : Nat := 4983230072969 + 3 ^ 40 * 1063884 * 2
def baseEnd_1063884 : Nat := 364189235085347188438195

theorem tailTrace_1063884 : CollatzResearch.WordTrace tailWord_1063884 prefixEnd_1063884 364189235085347188438195 := by
  unfold tailWord_1063884
  simp only [CollatzResearch.WordTrace]
  refine ⟨19401518638868719883339353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25868691518491626511119137 19401518638868719883339353)
  ·
    refine ⟨14551138979151539912504515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19401518638868719883339353 14551138979151539912504515)
    ·
      refine ⟨21826708468727309868756773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14551138979151539912504515 21826708468727309868756773)
      ·
        refine ⟨4092507837886370600391895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21826708468727309868756773 4092507837886370600391895)
        ·
          refine ⟨6138761756829555900587843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4092507837886370600391895 6138761756829555900587843)
          ·
            refine ⟨9208142635244333850881765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6138761756829555900587843 9208142635244333850881765)
            ·
              refine ⟨1726526744108312597040331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9208142635244333850881765 1726526744108312597040331)
              ·
                refine ⟨2589790116162468895560497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1726526744108312597040331 2589790116162468895560497)
                ·
                  refine ⟨1942342587121851671670373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2589790116162468895560497 1942342587121851671670373)
                  ·
                    refine ⟨364189235085347188438195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1942342587121851671670373 364189235085347188438195)
                    ·
                      rfl

theorem cell22_1063884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 2, 4].length) (baseStart_1063884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1063884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1063884 prefixEnd_1063884 := by exact prefixLift 1063884
  have htrace : WordTrace (prefixWord ++ tailWord_1063884) baseStart_1063884 baseEnd_1063884 := by
    simpa [prefixWord, tailWord_1063884, baseEnd_1063884] using wordTrace_append hprefix tailTrace_1063884
  have hstable : (prefixWord ++ tailWord_1063884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063884).length < 2 ^ (prefixWord ++ tailWord_1063884).sum := by decide
  have hdescent : baseEnd_1063884 < baseStart_1063884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063912 : List Nat := [2, 1, 4, 1, 1, 1, 3, 1, 2, 6]
def baseStart_1063912 : Nat := 118140960795 + 1063912 * 2 ^ 59
def prefixEnd_1063912 : Nat := 4983230072969 + 3 ^ 40 * 1063912 * 2
def baseEnd_1063912 : Nat := 364198820057564448738109

theorem tailTrace_1063912 : CollatzResearch.WordTrace tailWord_1063912 prefixEnd_1063912 364198820057564448738109 := by
  unfold tailWord_1063912
  simp only [CollatzResearch.WordTrace]
  refine ⟨19402029260818000274348995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25869372347757333699131993 19402029260818000274348995)
  ·
    refine ⟨29103043891227000411523493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19402029260818000274348995 29103043891227000411523493)
    ·
      refine ⟨5456820729605062577160655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29103043891227000411523493 5456820729605062577160655)
      ·
        refine ⟨8185231094407593865740983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5456820729605062577160655 8185231094407593865740983)
        ·
          refine ⟨12277846641611390798611475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8185231094407593865740983 12277846641611390798611475)
          ·
            refine ⟨18416769962417086197917213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12277846641611390798611475 18416769962417086197917213)
            ·
              refine ⟨6906288735906407324218955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18416769962417086197917213 6906288735906407324218955)
              ·
                refine ⟨10359433103859610986328433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6906288735906407324218955 10359433103859610986328433)
                ·
                  refine ⟨7769574827894708239746325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10359433103859610986328433 7769574827894708239746325)
                  ·
                    refine ⟨364198820057564448738109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7769574827894708239746325 364198820057564448738109)
                    ·
                      rfl

theorem cell22_1063912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_1063912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1063912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1063912 prefixEnd_1063912 := by exact prefixLift 1063912
  have htrace : WordTrace (prefixWord ++ tailWord_1063912) baseStart_1063912 baseEnd_1063912 := by
    simpa [prefixWord, tailWord_1063912, baseEnd_1063912] using wordTrace_append hprefix tailTrace_1063912
  have hstable : (prefixWord ++ tailWord_1063912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063912).length < 2 ^ (prefixWord ++ tailWord_1063912).sum := by decide
  have hdescent : baseEnd_1063912 < baseStart_1063912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063948 : List Nat := [2, 2, 1, 2, 3, 3, 2, 3, 1, 3]
def baseStart_1063948 : Nat := 118140960795 + 1063948 * 2 ^ 59
def prefixEnd_1063948 : Nat := 4983230072969 + 3 ^ 40 * 1063948 * 2
def baseEnd_1063948 : Nat := 364211143593272354837999

theorem tailTrace_1063948 : CollatzResearch.WordTrace tailWord_1063948 prefixEnd_1063948 364211143593272354837999 := by
  unfold tailWord_1063948
  simp only [CollatzResearch.WordTrace]
  refine ⟨19402685774752789348504249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25870247699670385798005665 19402685774752789348504249)
  ·
    refine ⟨14552014331064592011378187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19402685774752789348504249 14552014331064592011378187)
    ·
      refine ⟨21828021496596888017067281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14552014331064592011378187 21828021496596888017067281)
      ·
        refine ⟨16371016122447666012800461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21828021496596888017067281 16371016122447666012800461)
        ·
          refine ⟨6139131045917874754800173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16371016122447666012800461 6139131045917874754800173)
          ·
            refine ⟨2302174142219203033050065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6139131045917874754800173 2302174142219203033050065)
            ·
              refine ⟨1726630606664402274787549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2302174142219203033050065 1726630606664402274787549)
              ·
                refine ⟨647486477499150853045331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1726630606664402274787549 647486477499150853045331)
                ·
                  refine ⟨971229716248726279567997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 647486477499150853045331 971229716248726279567997)
                  ·
                    refine ⟨364211143593272354837999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 971229716248726279567997 364211143593272354837999)
                    ·
                      rfl

theorem cell22_1063948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 3, 1, 3].length) (baseStart_1063948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1063948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1063948 prefixEnd_1063948 := by exact prefixLift 1063948
  have htrace : WordTrace (prefixWord ++ tailWord_1063948) baseStart_1063948 baseEnd_1063948 := by
    simpa [prefixWord, tailWord_1063948, baseEnd_1063948] using wordTrace_append hprefix tailTrace_1063948
  have hstable : (prefixWord ++ tailWord_1063948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063948).length < 2 ^ (prefixWord ++ tailWord_1063948).sum := by decide
  have hdescent : baseEnd_1063948 < baseStart_1063948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063954 : List Nat := [3, 2, 5, 1, 2, 1, 1, 2, 2, 3]
def baseStart_1063954 : Nat := 118140960795 + 1063954 * 2 ^ 59
def prefixEnd_1063954 : Nat := 4983230072969 + 3 ^ 40 * 1063954 * 2
def baseEnd_1063954 : Nat := 364213197515890339187981

theorem tailTrace_1063954 : CollatzResearch.WordTrace tailWord_1063954 prefixEnd_1063954 364213197515890339187981 := by
  unfold tailWord_1063954
  simp only [CollatzResearch.WordTrace]
  refine ⟨9701397596870960430431729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25870393591655894481151277 9701397596870960430431729)
  ·
    refine ⟨7276048197653220322823797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9701397596870960430431729 7276048197653220322823797)
    ·
      refine ⟨682129518529989405264731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7276048197653220322823797 682129518529989405264731)
      ·
        refine ⟨1023194277794984107897097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 682129518529989405264731 1023194277794984107897097)
        ·
          refine ⟨767395708346238080922823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1023194277794984107897097 767395708346238080922823)
          ·
            refine ⟨1151093562519357121384235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 767395708346238080922823 1151093562519357121384235)
            ·
              refine ⟨1726640343779035682076353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1151093562519357121384235 1726640343779035682076353)
              ·
                refine ⟨1294980257834276761557265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1726640343779035682076353 1294980257834276761557265)
                ·
                  refine ⟨971235193375707571167949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1294980257834276761557265 971235193375707571167949)
                  ·
                    refine ⟨364213197515890339187981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 971235193375707571167949 364213197515890339187981)
                    ·
                      rfl

theorem cell22_1063954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_1063954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1063954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1063954 prefixEnd_1063954 := by exact prefixLift 1063954
  have htrace : WordTrace (prefixWord ++ tailWord_1063954) baseStart_1063954 baseEnd_1063954 := by
    simpa [prefixWord, tailWord_1063954, baseEnd_1063954] using wordTrace_append hprefix tailTrace_1063954
  have hstable : (prefixWord ++ tailWord_1063954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063954).length < 2 ^ (prefixWord ++ tailWord_1063954).sum := by decide
  have hdescent : baseEnd_1063954 < baseStart_1063954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063959 : List Nat := [1, 1, 3, 5, 1, 1, 1, 2, 2, 5]
def baseStart_1063959 : Nat := 118140960795 + 1063959 * 2 ^ 59
def prefixEnd_1063959 : Nat := 4983230072969 + 3 ^ 40 * 1063959 * 2
def baseEnd_1063959 : Nat := 364214909118071992812965

theorem tailTrace_1063959 : CollatzResearch.WordTrace tailWord_1063959 prefixEnd_1063959 364214909118071992812965 := by
  unfold tailWord_1063959
  simp only [CollatzResearch.WordTrace]
  refine ⟨38805772752465727575658931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25870515168310485050439287 38805772752465727575658931)
  ·
    refine ⟨58208659128698591363488397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38805772752465727575658931 58208659128698591363488397)
    ·
      refine ⟨21828247173261971761308149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58208659128698591363488397 21828247173261971761308149)
      ·
        refine ⟨2046398172493309852622639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21828247173261971761308149 2046398172493309852622639)
        ·
          refine ⟨3069597258739964778933959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2046398172493309852622639 3069597258739964778933959)
          ·
            refine ⟨4604395888109947168400939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3069597258739964778933959 4604395888109947168400939)
            ·
              refine ⟨6906593832164920752601409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4604395888109947168400939 6906593832164920752601409)
              ·
                refine ⟨5179945374123690564451057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6906593832164920752601409 5179945374123690564451057)
                ·
                  refine ⟨3884959030592767923338293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5179945374123690564451057 3884959030592767923338293)
                  ·
                    refine ⟨364214909118071992812965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3884959030592767923338293 364214909118071992812965)
                    ·
                      rfl

theorem cell22_1063959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 5].length) (baseStart_1063959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1063959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1063959 prefixEnd_1063959 := by exact prefixLift 1063959
  have htrace : WordTrace (prefixWord ++ tailWord_1063959) baseStart_1063959 baseEnd_1063959 := by
    simpa [prefixWord, tailWord_1063959, baseEnd_1063959] using wordTrace_append hprefix tailTrace_1063959
  have hstable : (prefixWord ++ tailWord_1063959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063959).length < 2 ^ (prefixWord ++ tailWord_1063959).sum := by decide
  have hdescent : baseEnd_1063959 < baseStart_1063959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063978 : List Nat := [3, 1, 4, 1, 3, 1, 3, 1, 5]
def baseStart_1063978 : Nat := 118140960795 + 1063978 * 2 ^ 59
def prefixEnd_1063978 : Nat := 4983230072969 + 3 ^ 40 * 1063978 * 2
def baseEnd_1063978 : Nat := 121407137735454092195969

theorem tailTrace_1063978 : CollatzResearch.WordTrace tailWord_1063978 prefixEnd_1063978 121407137735454092195969 := by
  unfold tailWord_1063978
  simp only [CollatzResearch.WordTrace]
  refine ⟨9701616434849223455150147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25870977159597929213733725 9701616434849223455150147)
  ·
    refine ⟨14552424652273835182725221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9701616434849223455150147 14552424652273835182725221)
    ·
      refine ⟨2728579622301344096760979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14552424652273835182725221 2728579622301344096760979)
      ·
        refine ⟨4092869433452016145141469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2728579622301344096760979 4092869433452016145141469)
        ·
          refine ⟨1534826037544506054428051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4092869433452016145141469 1534826037544506054428051)
          ·
            refine ⟨2302239056316759081642077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1534826037544506054428051 2302239056316759081642077)
            ·
              refine ⟨863339646118784655615779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2302239056316759081642077 863339646118784655615779)
              ·
                refine ⟨1295009469178176983423669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 863339646118784655615779 1295009469178176983423669)
                ·
                  refine ⟨121407137735454092195969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1295009469178176983423669 121407137735454092195969)
                  ·
                    rfl

theorem cell22_1063978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 1, 5].length) (baseStart_1063978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1063978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1063978 prefixEnd_1063978 := by exact prefixLift 1063978
  have htrace : WordTrace (prefixWord ++ tailWord_1063978) baseStart_1063978 baseEnd_1063978 := by
    simpa [prefixWord, tailWord_1063978, baseEnd_1063978] using wordTrace_append hprefix tailTrace_1063978
  have hstable : (prefixWord ++ tailWord_1063978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063978).length < 2 ^ (prefixWord ++ tailWord_1063978).sum := by decide
  have hdescent : baseEnd_1063978 < baseStart_1063978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064017 : List Nat := [1, 2, 2, 1, 3, 1, 12]
def baseStart_1064017 : Nat := 118140960795 + 1064017 * 2 ^ 59
def prefixEnd_1064017 : Nat := 4983230072969 + 3 ^ 40 * 1064017 * 2
def baseEnd_1064017 : Nat := 13490176433458487957881

theorem tailTrace_1064017 : CollatzResearch.WordTrace tailWord_1064017 prefixEnd_1064017 13490176433458487957881 := by
  unfold tailWord_1064017
  simp only [CollatzResearch.WordTrace]
  refine ⟨38807888186255603481270305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25871925457503735654180203 38807888186255603481270305)
  ·
    refine ⟨29105916139691702610952729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38807888186255603481270305 29105916139691702610952729)
    ·
      refine ⟨21829437104768776958214547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29105916139691702610952729 21829437104768776958214547)
      ·
        refine ⟨32744155657153165437321821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21829437104768776958214547 32744155657153165437321821)
        ·
          refine ⟨12279058371432437038995683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32744155657153165437321821 12279058371432437038995683)
          ·
            refine ⟨18418587557148655558493525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12279058371432437038995683 18418587557148655558493525)
            ·
              refine ⟨13490176433458487957881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 18418587557148655558493525 13490176433458487957881)
              ·
                rfl

theorem cell22_1064017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 12].length) (baseStart_1064017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1064017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1064017 prefixEnd_1064017 := by exact prefixLift 1064017
  have htrace : WordTrace (prefixWord ++ tailWord_1064017) baseStart_1064017 baseEnd_1064017 := by
    simpa [prefixWord, tailWord_1064017, baseEnd_1064017] using wordTrace_append hprefix tailTrace_1064017
  have hstable : (prefixWord ++ tailWord_1064017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064017).length < 2 ^ (prefixWord ++ tailWord_1064017).sum := by decide
  have hdescent : baseEnd_1064017 < baseStart_1064017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064021 : List Nat := [1, 3, 2, 2, 1, 2, 2, 4, 2, 3]
def baseStart_1064021 : Nat := 118140960795 + 1064021 * 2 ^ 59
def prefixEnd_1064021 : Nat := 4983230072969 + 3 ^ 40 * 1064021 * 2
def baseEnd_1064021 : Nat := 364236132985124497762775

theorem tailTrace_1064021 : CollatzResearch.WordTrace tailWord_1064021 prefixEnd_1064021 364236132985124497762775 := by
  unfold tailWord_1064021
  simp only [CollatzResearch.WordTrace]
  refine ⟨38808034078241112164415917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25872022718827408109610611 38808034078241112164415917)
  ·
    refine ⟨14553012779340417061655969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38808034078241112164415917 14553012779340417061655969)
    ·
      refine ⟨10914759584505312796241977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14553012779340417061655969 10914759584505312796241977)
      ·
        refine ⟨8186069688378984597181483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10914759584505312796241977 8186069688378984597181483)
        ·
          refine ⟨12279104532568476895772225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8186069688378984597181483 12279104532568476895772225)
          ·
            refine ⟨9209328399426357671829169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12279104532568476895772225 9209328399426357671829169)
            ·
              refine ⟨6906996299569768253871877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9209328399426357671829169 6906996299569768253871877)
              ·
                refine ⟨1295061806169331547600977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6906996299569768253871877 1295061806169331547600977)
                ·
                  refine ⟨971296354626998660700733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1295061806169331547600977 971296354626998660700733)
                  ·
                    refine ⟨364236132985124497762775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 971296354626998660700733 364236132985124497762775)
                    ·
                      rfl

theorem cell22_1064021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 4, 2, 3].length) (baseStart_1064021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1064021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1064021 prefixEnd_1064021 := by exact prefixLift 1064021
  have htrace : WordTrace (prefixWord ++ tailWord_1064021) baseStart_1064021 baseEnd_1064021 := by
    simpa [prefixWord, tailWord_1064021, baseEnd_1064021] using wordTrace_append hprefix tailTrace_1064021
  have hstable : (prefixWord ++ tailWord_1064021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064021).length < 2 ^ (prefixWord ++ tailWord_1064021).sum := by decide
  have hdescent : baseEnd_1064021 < baseStart_1064021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064130 : List Nat := [3, 5, 1, 1, 2, 1, 1, 1, 7]
def baseStart_1064130 : Nat := 118140960795 + 1064130 * 2 ^ 59
def prefixEnd_1064130 : Nat := 4983230072969 + 3 ^ 40 * 1064130 * 2
def baseEnd_1064130 : Nat := 121424481970894848929147

theorem tailTrace_1064130 : CollatzResearch.WordTrace tailWord_1064130 prefixEnd_1064130 121424481970894848929147 := by
  unfold tailWord_1064130
  simp only [CollatzResearch.WordTrace]
  refine ⟨9703002408711555945033461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25874673089897482520089229 9703002408711555945033461)
  ·
    refine ⟨909656475816708369846887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9703002408711555945033461 909656475816708369846887)
    ·
      refine ⟨1364484713725062554770331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 909656475816708369846887 1364484713725062554770331)
      ·
        refine ⟨2046727070587593832155497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1364484713725062554770331 2046727070587593832155497)
        ·
          refine ⟨1535045302940695374116623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2046727070587593832155497 1535045302940695374116623)
          ·
            refine ⟨2302567954411043061174935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1535045302940695374116623 2302567954411043061174935)
            ·
              refine ⟨3453851931616564591762403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2302567954411043061174935 3453851931616564591762403)
              ·
                refine ⟨5180777897424846887643605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3453851931616564591762403 5180777897424846887643605)
                ·
                  refine ⟨121424481970894848929147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5180777897424846887643605 121424481970894848929147)
                  ·
                    rfl

theorem cell22_1064130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_1064130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1064130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1064130 prefixEnd_1064130 := by exact prefixLift 1064130
  have htrace : WordTrace (prefixWord ++ tailWord_1064130) baseStart_1064130 baseEnd_1064130 := by
    simpa [prefixWord, tailWord_1064130, baseEnd_1064130] using wordTrace_append hprefix tailTrace_1064130
  have hstable : (prefixWord ++ tailWord_1064130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064130).length < 2 ^ (prefixWord ++ tailWord_1064130).sum := by decide
  have hdescent : baseEnd_1064130 < baseStart_1064130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064134 : List Nat := [6, 1, 2, 2, 1, 1, 2, 1, 3, 3]
def baseStart_1064134 : Nat := 118140960795 + 1064134 * 2 ^ 59
def prefixEnd_1064134 : Nat := 4983230072969 + 3 ^ 40 * 1064134 * 2
def baseEnd_1064134 : Nat := 364274815194429869687429

theorem tailTrace_1064134 : CollatzResearch.WordTrace tailWord_1064134 prefixEnd_1064134 364274815194429869687429 := by
  unfold tailWord_1064134
  simp only [CollatzResearch.WordTrace]
  refine ⟨1212879860213491639477483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 25874770351221154975519637 1212879860213491639477483)
  ·
    refine ⟨1819319790320237459216225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1212879860213491639477483 1819319790320237459216225)
    ·
      refine ⟨1364489842740178094412169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1819319790320237459216225 1364489842740178094412169)
      ·
        refine ⟨1023367382055133570809127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1364489842740178094412169 1023367382055133570809127)
        ·
          refine ⟨1535051073082700356213691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1023367382055133570809127 1535051073082700356213691)
          ·
            refine ⟨2302576609624050534320537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1535051073082700356213691 2302576609624050534320537)
            ·
              refine ⟨1726932457218037900740403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2302576609624050534320537 1726932457218037900740403)
              ·
                refine ⟨2590398685827056851110605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1726932457218037900740403 2590398685827056851110605)
                ·
                  refine ⟨971399507185146319166477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2590398685827056851110605 971399507185146319166477)
                  ·
                    refine ⟨364274815194429869687429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 971399507185146319166477 364274815194429869687429)
                    ·
                      rfl

theorem cell22_1064134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_1064134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1064134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1064134 prefixEnd_1064134 := by exact prefixLift 1064134
  have htrace : WordTrace (prefixWord ++ tailWord_1064134) baseStart_1064134 baseEnd_1064134 := by
    simpa [prefixWord, tailWord_1064134, baseEnd_1064134] using wordTrace_append hprefix tailTrace_1064134
  have hstable : (prefixWord ++ tailWord_1064134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064134).length < 2 ^ (prefixWord ++ tailWord_1064134).sum := by decide
  have hdescent : baseEnd_1064134 < baseStart_1064134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064173 : List Nat := [1, 5, 1, 2, 2, 1, 1, 2, 4, 3]
def baseStart_1064173 : Nat := 118140960795 + 1064173 * 2 ^ 59
def prefixEnd_1064173 : Nat := 4983230072969 + 3 ^ 40 * 1064173 * 2
def baseEnd_1064173 : Nat := 364288165691446767962309

theorem tailTrace_1064173 : CollatzResearch.WordTrace tailWord_1064173 prefixEnd_1064173 364288165691446767962309 := by
  unfold tailWord_1064173
  simp only [CollatzResearch.WordTrace]
  refine ⟨38813577973690442123949173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25875718649126961415966115 38813577973690442123949173)
  ·
    refine ⟨3638772935033478949120235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38813577973690442123949173 3638772935033478949120235)
    ·
      refine ⟨5458159402550218423680353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3638772935033478949120235 5458159402550218423680353)
      ·
        refine ⟨4093619551912663817760265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5458159402550218423680353 4093619551912663817760265)
        ·
          refine ⟨3070214663934497863320199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4093619551912663817760265 3070214663934497863320199)
          ·
            refine ⟨4605321995901746794980299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3070214663934497863320199 4605321995901746794980299)
            ·
              refine ⟨6907982993852620192470449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4605321995901746794980299 6907982993852620192470449)
              ·
                refine ⟨5180987245389465144352837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6907982993852620192470449 5180987245389465144352837)
                ·
                  refine ⟨971435108510524714566157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5180987245389465144352837 971435108510524714566157)
                  ·
                    refine ⟨364288165691446767962309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 971435108510524714566157 364288165691446767962309)
                    ·
                      rfl

theorem cell22_1064173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_1064173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1064173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1064173 prefixEnd_1064173 := by exact prefixLift 1064173
  have htrace : WordTrace (prefixWord ++ tailWord_1064173) baseStart_1064173 baseEnd_1064173 := by
    simpa [prefixWord, tailWord_1064173, baseEnd_1064173] using wordTrace_append hprefix tailTrace_1064173
  have hstable : (prefixWord ++ tailWord_1064173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064173).length < 2 ^ (prefixWord ++ tailWord_1064173).sum := by decide
  have hdescent : baseEnd_1064173 < baseStart_1064173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064175 : List Nat := [1, 1, 2, 1, 7, 2, 1, 3, 4]
def baseStart_1064175 : Nat := 118140960795 + 1064175 * 2 ^ 59
def prefixEnd_1064175 : Nat := 4983230072969 + 3 ^ 40 * 1064175 * 2
def baseEnd_1064175 : Nat := 121429616777439809804101

theorem tailTrace_1064175 : CollatzResearch.WordTrace tailWord_1064175 prefixEnd_1064175 121429616777439809804101 := by
  unfold tailWord_1064175
  simp only [CollatzResearch.WordTrace]
  refine ⟨38813650919683196465521979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25875767279788797643681319 38813650919683196465521979)
  ·
    refine ⟨58220476379524794698282969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38813650919683196465521979 58220476379524794698282969)
    ·
      refine ⟨43665357284643596023712227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58220476379524794698282969 43665357284643596023712227)
      ·
        refine ⟨65498035926965394035568341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43665357284643596023712227 65498035926965394035568341)
        ·
          refine ⟨1535110217038251422708633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 65498035926965394035568341 1535110217038251422708633)
          ·
            refine ⟨1151332662778688567031475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1535110217038251422708633 1151332662778688567031475)
            ·
              refine ⟨1726998994168032850547213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1151332662778688567031475 1726998994168032850547213)
              ·
                refine ⟨647624622813012318955205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1726998994168032850547213 647624622813012318955205)
                ·
                  refine ⟨121429616777439809804101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 647624622813012318955205 121429616777439809804101)
                  ·
                    rfl

theorem cell22_1064175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 3, 4].length) (baseStart_1064175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1064175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1064175 prefixEnd_1064175 := by exact prefixLift 1064175
  have htrace : WordTrace (prefixWord ++ tailWord_1064175) baseStart_1064175 baseEnd_1064175 := by
    simpa [prefixWord, tailWord_1064175, baseEnd_1064175] using wordTrace_append hprefix tailTrace_1064175
  have hstable : (prefixWord ++ tailWord_1064175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064175).length < 2 ^ (prefixWord ++ tailWord_1064175).sum := by decide
  have hdescent : baseEnd_1064175 < baseStart_1064175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064188 : List Nat := [2, 2, 2, 1, 5, 1, 1, 2, 2, 4]
def baseStart_1064188 : Nat := 118140960795 + 1064188 * 2 ^ 59
def prefixEnd_1064188 : Nat := 4983230072969 + 3 ^ 40 * 1064188 * 2
def baseEnd_1064188 : Nat := 364293300497991728837263

theorem tailTrace_1064188 : CollatzResearch.WordTrace tailWord_1064188 prefixEnd_1064188 364293300497991728837263 := by
  unfold tailWord_1064188
  simp only [CollatzResearch.WordTrace]
  refine ⟨19407062534318049842872609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25876083379090733123830145 19407062534318049842872609)
  ·
    refine ⟨14555296900738537382154457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19407062534318049842872609 14555296900738537382154457)
    ·
      refine ⟨10916472675553903036615843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14555296900738537382154457 10916472675553903036615843)
      ·
        refine ⟨16374709013330854554923765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10916472675553903036615843 16374709013330854554923765)
        ·
          refine ⟨1535128969999767614524103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16374709013330854554923765 1535128969999767614524103)
          ·
            refine ⟨2302693454999651421786155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1535128969999767614524103 2302693454999651421786155)
            ·
              refine ⟨3454040182499477132679233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2302693454999651421786155 3454040182499477132679233)
              ·
                refine ⟨2590530136874607849509425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3454040182499477132679233 2590530136874607849509425)
                ·
                  refine ⟨1942897602655955887132069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2590530136874607849509425 1942897602655955887132069)
                  ·
                    refine ⟨364293300497991728837263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1942897602655955887132069 364293300497991728837263)
                    ·
                      rfl

theorem cell22_1064188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_1064188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1064188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1064188 prefixEnd_1064188 := by exact prefixLift 1064188
  have htrace : WordTrace (prefixWord ++ tailWord_1064188) baseStart_1064188 baseEnd_1064188 := by
    simpa [prefixWord, tailWord_1064188, baseEnd_1064188] using wordTrace_append hprefix tailTrace_1064188
  have hstable : (prefixWord ++ tailWord_1064188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064188).length < 2 ^ (prefixWord ++ tailWord_1064188).sum := by decide
  have hdescent : baseEnd_1064188 < baseStart_1064188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064222 : List Nat := [4, 3, 2, 1, 2, 1, 2, 1, 2, 4]
def baseStart_1064222 : Nat := 118140960795 + 1064222 * 2 ^ 59
def prefixEnd_1064222 : Nat := 4983230072969 + 3 ^ 40 * 1064222 * 2
def baseEnd_1064222 : Nat := 364304939392826973487159

theorem tailTrace_1064222 : CollatzResearch.WordTrace tailWord_1064222 prefixEnd_1064222 364304939392826973487159 := by
  unfold tailWord_1064222
  simp only [CollatzResearch.WordTrace]
  refine ⟨4851920643814115436560365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25876910100341948994988613 4851920643814115436560365)
  ·
    refine ⟨1819470241430293288710137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4851920643814115436560365 1819470241430293288710137)
    ·
      refine ⟨1364602681072719966532603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1819470241430293288710137 1364602681072719966532603)
      ·
        refine ⟨2046904021609079949798905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1364602681072719966532603 2046904021609079949798905)
        ·
          refine ⟨1535178016206809962349179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2046904021609079949798905 1535178016206809962349179)
          ·
            refine ⟨2302767024310214943523769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1535178016206809962349179 2302767024310214943523769)
            ·
              refine ⟨1727075268232661207642827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2302767024310214943523769 1727075268232661207642827)
              ·
                refine ⟨2590612902348991811464241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1727075268232661207642827 2590612902348991811464241)
                ·
                  refine ⟨1942959676761743858598181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2590612902348991811464241 1942959676761743858598181)
                  ·
                    refine ⟨364304939392826973487159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1942959676761743858598181 364304939392826973487159)
                    ·
                      rfl

theorem cell22_1064222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_1064222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1064222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1064222 prefixEnd_1064222 := by exact prefixLift 1064222
  have htrace : WordTrace (prefixWord ++ tailWord_1064222) baseStart_1064222 baseEnd_1064222 := by
    simpa [prefixWord, tailWord_1064222, baseEnd_1064222] using wordTrace_append hprefix tailTrace_1064222
  have hstable : (prefixWord ++ tailWord_1064222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064222).length < 2 ^ (prefixWord ++ tailWord_1064222).sum := by decide
  have hdescent : baseEnd_1064222 < baseStart_1064222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064252 : List Nat := [2, 2, 2, 2, 1, 3, 4, 2, 1, 3]
def baseStart_1064252 : Nat := 118140960795 + 1064252 * 2 ^ 59
def prefixEnd_1064252 : Nat := 4983230072969 + 3 ^ 40 * 1064252 * 2
def baseEnd_1064252 : Nat := 364315209005916895237067

theorem tailTrace_1064252 : CollatzResearch.WordTrace tailWord_1064252 prefixEnd_1064252 364315209005916895237067 := by
  unfold tailWord_1064252
  simp only [CollatzResearch.WordTrace]
  refine ⟨19408229670202119308037505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25877639560269492410716673 19408229670202119308037505)
  ·
    refine ⟨14556172252651589481028129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19408229670202119308037505 14556172252651589481028129)
    ·
      refine ⟨10917129189488692110771097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14556172252651589481028129 10917129189488692110771097)
      ·
        refine ⟨8187846892116519083078323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10917129189488692110771097 8187846892116519083078323)
        ·
          refine ⟨12281770338174778624617485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8187846892116519083078323 12281770338174778624617485)
          ·
            refine ⟨4605663876815541984231557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12281770338174778624617485 4605663876815541984231557)
            ·
              refine ⟨863561976902914122043417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4605663876815541984231557 863561976902914122043417)
              ·
                refine ⟨647671482677185591532563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 863561976902914122043417 647671482677185591532563)
                ·
                  refine ⟨971507224015778387298845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 647671482677185591532563 971507224015778387298845)
                  ·
                    refine ⟨364315209005916895237067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 971507224015778387298845 364315209005916895237067)
                    ·
                      rfl

theorem cell22_1064252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 2, 1, 3].length) (baseStart_1064252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1064252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1064252 prefixEnd_1064252 := by exact prefixLift 1064252
  have htrace : WordTrace (prefixWord ++ tailWord_1064252) baseStart_1064252 baseEnd_1064252 := by
    simpa [prefixWord, tailWord_1064252, baseEnd_1064252] using wordTrace_append hprefix tailTrace_1064252
  have hstable : (prefixWord ++ tailWord_1064252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064252).length < 2 ^ (prefixWord ++ tailWord_1064252).sum := by decide
  have hdescent : baseEnd_1064252 < baseStart_1064252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064295 : List Nat := [1, 1, 5, 1, 4, 1, 1, 3, 1, 4]
def baseStart_1064295 : Nat := 118140960795 + 1064295 * 2 ^ 59
def prefixEnd_1064295 : Nat := 4983230072969 + 3 ^ 40 * 1064295 * 2
def baseEnd_1064295 : Nat := 364329928784679116411935

theorem tailTrace_1064295 : CollatzResearch.WordTrace tailWord_1064295 prefixEnd_1064295 364329928784679116411935 := by
  unfold tailWord_1064295
  simp only [CollatzResearch.WordTrace]
  refine ⟨38818027679248456959890339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25878685119498971306593559 38818027679248456959890339)
  ·
    refine ⟨58227041518872685439835509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38818027679248456959890339 58227041518872685439835509)
    ·
      refine ⟨5458785142394314259984579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58227041518872685439835509 5458785142394314259984579)
      ·
        refine ⟨8188177713591471389976869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5458785142394314259984579 8188177713591471389976869)
        ·
          refine ⟨1535283321298400885620663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8188177713591471389976869 1535283321298400885620663)
          ·
            refine ⟨2302924981947601328430995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1535283321298400885620663 2302924981947601328430995)
            ·
              refine ⟨3454387472921401992646493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2302924981947601328430995 3454387472921401992646493)
              ·
                refine ⟨1295395302345525747242435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3454387472921401992646493 1295395302345525747242435)
                ·
                  refine ⟨1943092953518288620863653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1295395302345525747242435 1943092953518288620863653)
                  ·
                    refine ⟨364329928784679116411935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1943092953518288620863653 364329928784679116411935)
                    ·
                      rfl

theorem cell22_1064295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_1064295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1064295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1064295 prefixEnd_1064295 := by exact prefixLift 1064295
  have htrace : WordTrace (prefixWord ++ tailWord_1064295) baseStart_1064295 baseEnd_1064295 := by
    simpa [prefixWord, tailWord_1064295, baseEnd_1064295] using wordTrace_append hprefix tailTrace_1064295
  have hstable : (prefixWord ++ tailWord_1064295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064295).length < 2 ^ (prefixWord ++ tailWord_1064295).sum := by decide
  have hdescent : baseEnd_1064295 < baseStart_1064295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064344 : List Nat := [2, 1, 2, 5, 3, 1, 1, 3, 4]
def baseStart_1064344 : Nat := 118140960795 + 1064344 * 2 ^ 59
def prefixEnd_1064344 : Nat := 4983230072969 + 3 ^ 40 * 1064344 * 2
def baseEnd_1064344 : Nat := 121448900828686440645595

theorem tailTrace_1064344 : CollatzResearch.WordTrace tailWord_1064344 prefixEnd_1064344 121448900828686440645595 := by
  unfold tailWord_1064344
  simp only [CollatzResearch.WordTrace]
  refine ⟨19409907428035469164212043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25879876570713958885616057 19409907428035469164212043)
  ·
    refine ⟨29114861142053203746318065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19409907428035469164212043 29114861142053203746318065)
    ·
      refine ⟨21836145856539902809738549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29114861142053203746318065 21836145856539902809738549)
      ·
        refine ⟨2047138674050615888412989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21836145856539902809738549 2047138674050615888412989)
        ·
          refine ⟨767677002768980958154871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2047138674050615888412989 767677002768980958154871)
          ·
            refine ⟨1151515504153471437232307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 767677002768980958154871 1151515504153471437232307)
            ·
              refine ⟨1727273256230207155848461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1151515504153471437232307 1727273256230207155848461)
              ·
                refine ⟨647727471086327683443173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1727273256230207155848461 647727471086327683443173)
                ·
                  refine ⟨121448900828686440645595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 647727471086327683443173 121448900828686440645595)
                  ·
                    rfl

theorem cell22_1064344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 3, 4].length) (baseStart_1064344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1064344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1064344 prefixEnd_1064344 := by exact prefixLift 1064344
  have htrace : WordTrace (prefixWord ++ tailWord_1064344) baseStart_1064344 baseEnd_1064344 := by
    simpa [prefixWord, tailWord_1064344, baseEnd_1064344] using wordTrace_append hprefix tailTrace_1064344
  have hstable : (prefixWord ++ tailWord_1064344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064344).length < 2 ^ (prefixWord ++ tailWord_1064344).sum := by decide
  have hdescent : baseEnd_1064344 < baseStart_1064344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064421 : List Nat := [1, 3, 1, 5, 1, 3, 2, 2, 1, 3]
def baseStart_1064421 : Nat := 118140960795 + 1064421 * 2 ^ 59
def prefixEnd_1064421 : Nat := 4983230072969 + 3 ^ 40 * 1064421 * 2
def baseEnd_1064421 : Nat := 364373061159656787761549

theorem tailTrace_1064421 : CollatzResearch.WordTrace tailWord_1064421 prefixEnd_1064421 364373061159656787761549 := by
  unfold tailWord_1064421
  simp only [CollatzResearch.WordTrace]
  refine ⟨38822623276791980478977117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25881748851194653652651411 38822623276791980478977117)
  ·
    refine ⟨14558483728796992679616419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38822623276791980478977117 14558483728796992679616419)
    ·
      refine ⟨21837725593195489019424629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14558483728796992679616419 21837725593195489019424629)
      ·
        refine ⟨2047286774362077095571059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21837725593195489019424629 2047286774362077095571059)
        ·
          refine ⟨3070930161543115643356589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2047286774362077095571059 3070930161543115643356589)
          ·
            refine ⟨1151598810578668366258721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3070930161543115643356589 1151598810578668366258721)
            ·
              refine ⟨863699107934001274694041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1151598810578668366258721 863699107934001274694041)
              ·
                refine ⟨647774330950500956020531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 863699107934001274694041 647774330950500956020531)
                ·
                  refine ⟨971661496425751434030797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 647774330950500956020531 971661496425751434030797)
                  ·
                    refine ⟨364373061159656787761549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 971661496425751434030797 364373061159656787761549)
                    ·
                      rfl

theorem cell22_1064421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 2, 1, 3].length) (baseStart_1064421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1064421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1064421 prefixEnd_1064421 := by exact prefixLift 1064421
  have htrace : WordTrace (prefixWord ++ tailWord_1064421) baseStart_1064421 baseEnd_1064421 := by
    simpa [prefixWord, tailWord_1064421, baseEnd_1064421] using wordTrace_append hprefix tailTrace_1064421
  have hstable : (prefixWord ++ tailWord_1064421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064421).length < 2 ^ (prefixWord ++ tailWord_1064421).sum := by decide
  have hdescent : baseEnd_1064421 < baseStart_1064421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064552 : List Nat := [2, 1, 4, 3, 1, 2, 1, 3, 5]
def baseStart_1064552 : Nat := 118140960795 + 1064552 * 2 ^ 59
def prefixEnd_1064552 : Nat := 4983230072969 + 3 ^ 40 * 1064552 * 2
def baseEnd_1064552 : Nat := 121472635045605370912049

theorem tailTrace_1064552 : CollatzResearch.WordTrace tailWord_1064552 prefixEnd_1064552 121472635045605370912049 := by
  unfold tailWord_1064552
  simp only [CollatzResearch.WordTrace]
  refine ⟨19413700619658694925997955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25884934159544926567997273 19413700619658694925997955)
  ·
    refine ⟨29120550929488042388996933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19413700619658694925997955 29120550929488042388996933)
    ·
      refine ⟨5460103299279007947936925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29120550929488042388996933 5460103299279007947936925)
      ·
        refine ⟨2047538737229627980476347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5460103299279007947936925 2047538737229627980476347)
        ·
          refine ⟨3071308105844441970714521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2047538737229627980476347 3071308105844441970714521)
          ·
            refine ⟨2303481079383331478035891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3071308105844441970714521 2303481079383331478035891)
            ·
              refine ⟨3455221619074997217053837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2303481079383331478035891 3455221619074997217053837)
              ·
                refine ⟨1295708107153123956395189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3455221619074997217053837 1295708107153123956395189)
                ·
                  refine ⟨121472635045605370912049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1295708107153123956395189 121472635045605370912049)
                  ·
                    rfl

theorem cell22_1064552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 3, 5].length) (baseStart_1064552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1064552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1064552 prefixEnd_1064552 := by exact prefixLift 1064552
  have htrace : WordTrace (prefixWord ++ tailWord_1064552) baseStart_1064552 baseEnd_1064552 := by
    simpa [prefixWord, tailWord_1064552, baseEnd_1064552] using wordTrace_append hprefix tailTrace_1064552
  have hstable : (prefixWord ++ tailWord_1064552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064552).length < 2 ^ (prefixWord ++ tailWord_1064552).sum := by decide
  have hdescent : baseEnd_1064552 < baseStart_1064552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064612 : List Nat := [2, 3, 1, 2, 2, 3, 2, 1, 1, 5]
def baseStart_1064612 : Nat := 118140960795 + 1064612 * 2 ^ 59
def prefixEnd_1064612 : Nat := 4983230072969 + 3 ^ 40 * 1064612 * 2
def baseEnd_1064612 : Nat := 364438444362995956235963

theorem tailTrace_1064612 : CollatzResearch.WordTrace tailWord_1064612 prefixEnd_1064612 364438444362995956235963 := by
  unfold tailWord_1064612
  simp only [CollatzResearch.WordTrace]
  refine ⟨19414794809550010049590045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25886393079400013399453393 19414794809550010049590045)
  ·
    refine ⟨7280548053581253768596267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19414794809550010049590045 7280548053581253768596267)
    ·
      refine ⟨10920822080371880652894401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7280548053581253768596267 10920822080371880652894401)
      ·
        refine ⟨8190616560278910489670801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10920822080371880652894401 8190616560278910489670801)
        ·
          refine ⟨6142962420209182867253101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8190616560278910489670801 6142962420209182867253101)
          ·
            refine ⟨2303610907578443575219913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6142962420209182867253101 2303610907578443575219913)
            ·
              refine ⟨1727708180683832681414935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2303610907578443575219913 1727708180683832681414935)
              ·
                refine ⟨2591562271025749022122403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1727708180683832681414935 2591562271025749022122403)
                ·
                  refine ⟨3887343406538623533183605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2591562271025749022122403 3887343406538623533183605)
                  ·
                    refine ⟨364438444362995956235963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3887343406538623533183605 364438444362995956235963)
                    ·
                      rfl

theorem cell22_1064612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_1064612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1064612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1064612 prefixEnd_1064612 := by exact prefixLift 1064612
  have htrace : WordTrace (prefixWord ++ tailWord_1064612) baseStart_1064612 baseEnd_1064612 := by
    simpa [prefixWord, tailWord_1064612, baseEnd_1064612] using wordTrace_append hprefix tailTrace_1064612
  have hstable : (prefixWord ++ tailWord_1064612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064612).length < 2 ^ (prefixWord ++ tailWord_1064612).sum := by decide
  have hdescent : baseEnd_1064612 < baseStart_1064612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064657 : List Nat := [1, 2, 2, 1, 2, 4, 1, 3, 3, 3]
def baseStart_1064657 : Nat := 118140960795 + 1064657 * 2 ^ 59
def prefixEnd_1064657 : Nat := 4983230072969 + 3 ^ 40 * 1064657 * 2
def baseEnd_1064657 : Nat := 364453848782630838860825

theorem tailTrace_1064657 : CollatzResearch.WordTrace tailWord_1064657 prefixEnd_1064657 364453848782630838860825 := by
  unfold tailWord_1064657
  simp only [CollatzResearch.WordTrace]
  refine ⟨38831230903936992784568225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25887487269291328523045483 38831230903936992784568225)
  ·
    refine ⟨29123423177952744588426169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38831230903936992784568225 29123423177952744588426169)
    ·
      refine ⟨21842567383464558441319627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29123423177952744588426169 21842567383464558441319627)
      ·
        refine ⟨32763851075196837661979441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21842567383464558441319627 32763851075196837661979441)
        ·
          refine ⟨24572888306397628246484581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32763851075196837661979441 24572888306397628246484581)
          ·
            refine ⟨4607416557449555296215859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24572888306397628246484581 4607416557449555296215859)
            ·
              refine ⟨6911124836174332944323789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4607416557449555296215859 6911124836174332944323789)
              ·
                refine ⟨2591671813565374854121421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6911124836174332944323789 2591671813565374854121421)
                ·
                  refine ⟨971876930087015570295533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2591671813565374854121421 971876930087015570295533)
                  ·
                    refine ⟨364453848782630838860825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 971876930087015570295533 364453848782630838860825)
                    ·
                      rfl

theorem cell22_1064657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 3, 3].length) (baseStart_1064657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1064657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1064657 prefixEnd_1064657 := by exact prefixLift 1064657
  have htrace : WordTrace (prefixWord ++ tailWord_1064657) baseStart_1064657 baseEnd_1064657 := by
    simpa [prefixWord, tailWord_1064657, baseEnd_1064657] using wordTrace_append hprefix tailTrace_1064657
  have hstable : (prefixWord ++ tailWord_1064657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064657).length < 2 ^ (prefixWord ++ tailWord_1064657).sum := by decide
  have hdescent : baseEnd_1064657 < baseStart_1064657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064708 : List Nat := [2, 3, 2, 2, 1, 3, 3, 2, 1, 3]
def baseStart_1064708 : Nat := 118140960795 + 1064708 * 2 ^ 59
def prefixEnd_1064708 : Nat := 4983230072969 + 3 ^ 40 * 1064708 * 2
def baseEnd_1064708 : Nat := 364471307124883705835669

theorem tailTrace_1064708 : CollatzResearch.WordTrace tailWord_1064708 prefixEnd_1064708 364471307124883705835669 := by
  unfold tailWord_1064708
  simp only [CollatzResearch.WordTrace]
  refine ⟨19416545513376114247337389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25888727351168152329783185 19416545513376114247337389)
  ·
    refine ⟨7281204567516042842751521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19416545513376114247337389 7281204567516042842751521)
    ·
      refine ⟨5460903425637032132063641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7281204567516042842751521 5460903425637032132063641)
      ·
        refine ⟨4095677569227774099047731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5460903425637032132063641 4095677569227774099047731)
        ·
          refine ⟨6143516353841661148571597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4095677569227774099047731 6143516353841661148571597)
          ·
            refine ⟨2303818632690622930714349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6143516353841661148571597 2303818632690622930714349)
            ·
              refine ⟨863931987258983599017881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2303818632690622930714349 863931987258983599017881)
              ·
                refine ⟨647948990444237699263411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 863931987258983599017881 647948990444237699263411)
                ·
                  refine ⟨971923485666356548895117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 647948990444237699263411 971923485666356548895117)
                  ·
                    refine ⟨364471307124883705835669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 971923485666356548895117 364471307124883705835669)
                    ·
                      rfl

theorem cell22_1064708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_1064708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1064708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1064708 prefixEnd_1064708 := by exact prefixLift 1064708
  have htrace : WordTrace (prefixWord ++ tailWord_1064708) baseStart_1064708 baseEnd_1064708 := by
    simpa [prefixWord, tailWord_1064708, baseEnd_1064708] using wordTrace_append hprefix tailTrace_1064708
  have hstable : (prefixWord ++ tailWord_1064708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064708).length < 2 ^ (prefixWord ++ tailWord_1064708).sum := by decide
  have hdescent : baseEnd_1064708 < baseStart_1064708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064710 : List Nat := [6, 2, 2, 1, 1, 1, 2, 7]
def baseStart_1064710 : Nat := 118140960795 + 1064710 * 2 ^ 59
def prefixEnd_1064710 : Nat := 4983230072969 + 3 ^ 40 * 1064710 * 2
def baseEnd_1064710 : Nat := 40496887973972929698407

theorem tailTrace_1064710 : CollatzResearch.WordTrace tailWord_1064710 prefixEnd_1064710 40496887973972929698407 := by
  unfold tailWord_1064710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1213536374148280713632737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 25888775981829988557498389 1213536374148280713632737)
  ·
    refine ⟨910152280611210535224553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1213536374148280713632737 910152280611210535224553)
    ·
      refine ⟨682614210458407901418415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 910152280611210535224553 682614210458407901418415)
      ·
        refine ⟨1023921315687611852127623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 682614210458407901418415 1023921315687611852127623)
        ·
          refine ⟨1535881973531417778191435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1023921315687611852127623 1535881973531417778191435)
          ·
            refine ⟨2303822960297126667287153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1535881973531417778191435 2303822960297126667287153)
            ·
              refine ⟨1727867220222845000465365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2303822960297126667287153 1727867220222845000465365)
              ·
                refine ⟨40496887973972929698407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1727867220222845000465365 40496887973972929698407)
                ·
                  rfl

theorem cell22_1064710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_1064710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1064710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1064710 prefixEnd_1064710 := by exact prefixLift 1064710
  have htrace : WordTrace (prefixWord ++ tailWord_1064710) baseStart_1064710 baseEnd_1064710 := by
    simpa [prefixWord, tailWord_1064710, baseEnd_1064710] using wordTrace_append hprefix tailTrace_1064710
  have hstable : (prefixWord ++ tailWord_1064710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064710).length < 2 ^ (prefixWord ++ tailWord_1064710).sum := by decide
  have hdescent : baseEnd_1064710 < baseStart_1064710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064760 : List Nat := [2, 1, 2, 1, 3, 13]
def baseStart_1064760 : Nat := 118140960795 + 1064760 * 2 ^ 59
def prefixEnd_1064760 : Nat := 4983230072969 + 3 ^ 40 * 1064760 * 2
def baseEnd_1064760 : Nat := 4499865528241640784389

theorem tailTrace_1064760 : CollatzResearch.WordTrace tailWord_1064760 prefixEnd_1064760 4499865528241640784389 := by
  unfold tailWord_1064760
  simp only [CollatzResearch.WordTrace]
  refine ⟨19417493811281920687783867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25889991748375894250378489 19417493811281920687783867)
  ·
    refine ⟨29126240716922881031675801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19417493811281920687783867 29126240716922881031675801)
    ·
      refine ⟨21844680537692160773756851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29126240716922881031675801 21844680537692160773756851)
      ·
        refine ⟨32767020806538241160635277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21844680537692160773756851 32767020806538241160635277)
        ·
          refine ⟨12287632802451840435238229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32767020806538241160635277 12287632802451840435238229)
          ·
            refine ⟨4499865528241640784389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 12287632802451840435238229 4499865528241640784389)
            ·
              rfl

theorem cell22_1064760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 13].length) (baseStart_1064760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1064760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1064760 prefixEnd_1064760 := by exact prefixLift 1064760
  have htrace : WordTrace (prefixWord ++ tailWord_1064760) baseStart_1064760 baseEnd_1064760 := by
    simpa [prefixWord, tailWord_1064760, baseEnd_1064760] using wordTrace_append hprefix tailTrace_1064760
  have hstable : (prefixWord ++ tailWord_1064760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064760).length < 2 ^ (prefixWord ++ tailWord_1064760).sum := by decide
  have hdescent : baseEnd_1064760 < baseStart_1064760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064764 : List Nat := [2, 2, 2, 2, 1, 1, 3, 4, 2, 3]
def baseStart_1064764 : Nat := 118140960795 + 1064764 * 2 ^ 59
def prefixEnd_1064764 : Nat := 4983230072969 + 3 ^ 40 * 1064764 * 2
def baseEnd_1064764 : Nat := 364490477069318226435497

theorem tailTrace_1064764 : CollatzResearch.WordTrace tailWord_1064764 prefixEnd_1064764 364490477069318226435497 := by
  unfold tailWord_1064764
  simp only [CollatzResearch.WordTrace]
  refine ⟨19417566757274675029356673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25890089009699566705808897 19417566757274675029356673)
  ·
    refine ⟨14563175067956006272017505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19417566757274675029356673 14563175067956006272017505)
    ·
      refine ⟨10922381300967004704013129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14563175067956006272017505 10922381300967004704013129)
      ·
        refine ⟨8191785975725253528009847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10922381300967004704013129 8191785975725253528009847)
        ·
          refine ⟨12287678963587880292014771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8191785975725253528009847 12287678963587880292014771)
          ·
            refine ⟨18431518445381820438022157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12287678963587880292014771 18431518445381820438022157)
            ·
              refine ⟨6911819417018182664258309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18431518445381820438022157 6911819417018182664258309)
              ·
                refine ⟨1295966140690909249548433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6911819417018182664258309 1295966140690909249548433)
                ·
                  refine ⟨971974605518181937161325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1295966140690909249548433 971974605518181937161325)
                  ·
                    refine ⟨364490477069318226435497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 971974605518181937161325 364490477069318226435497)
                    ·
                      rfl

theorem cell22_1064764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 4, 2, 3].length) (baseStart_1064764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1064764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1064764 prefixEnd_1064764 := by exact prefixLift 1064764
  have htrace : WordTrace (prefixWord ++ tailWord_1064764) baseStart_1064764 baseEnd_1064764 := by
    simpa [prefixWord, tailWord_1064764, baseEnd_1064764] using wordTrace_append hprefix tailTrace_1064764
  have hstable : (prefixWord ++ tailWord_1064764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064764).length < 2 ^ (prefixWord ++ tailWord_1064764).sum := by decide
  have hdescent : baseEnd_1064764 < baseStart_1064764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064766 : List Nat := [4, 2, 1, 2, 2, 2, 1, 4, 4]
def baseStart_1064766 : Nat := 118140960795 + 1064766 * 2 ^ 59
def prefixEnd_1064766 : Nat := 4983230072969 + 3 ^ 40 * 1064766 * 2
def baseEnd_1064766 : Nat := 121497053903396962628497

theorem tailTrace_1064766 : CollatzResearch.WordTrace tailWord_1064766 prefixEnd_1064766 121497053903396962628497 := by
  unfold tailWord_1064766
  simp only [CollatzResearch.WordTrace]
  refine ⟨4854400807567763050035769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25890137640361402933524101 4854400807567763050035769)
  ·
    refine ⟨3640800605675822287526827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4854400807567763050035769 3640800605675822287526827)
    ·
      refine ⟨5461200908513733431290241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3640800605675822287526827 5461200908513733431290241)
      ·
        refine ⟨4095900681385300073467681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5461200908513733431290241 4095900681385300073467681)
        ·
          refine ⟨3071925511038975055100761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4095900681385300073467681 3071925511038975055100761)
          ·
            refine ⟨2303944133279231291325571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3071925511038975055100761 2303944133279231291325571)
            ·
              refine ⟨3455916199918846936988357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2303944133279231291325571 3455916199918846936988357)
              ·
                refine ⟨647984287484783800685317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3455916199918846936988357 647984287484783800685317)
                ·
                  refine ⟨121497053903396962628497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 647984287484783800685317 121497053903396962628497)
                  ·
                    rfl

theorem cell22_1064766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_1064766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1064766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1064766 prefixEnd_1064766 := by exact prefixLift 1064766
  have htrace : WordTrace (prefixWord ++ tailWord_1064766) baseStart_1064766 baseEnd_1064766 := by
    simpa [prefixWord, tailWord_1064766, baseEnd_1064766] using wordTrace_append hprefix tailTrace_1064766
  have hstable : (prefixWord ++ tailWord_1064766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064766).length < 2 ^ (prefixWord ++ tailWord_1064766).sum := by decide
  have hdescent : baseEnd_1064766 < baseStart_1064766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064781 : List Nat := [1, 6, 1, 2, 1, 2, 2, 1, 1, 5]
def baseStart_1064781 : Nat := 118140960795 + 1064781 * 2 ^ 59
def prefixEnd_1064781 : Nat := 4983230072969 + 3 ^ 40 * 1064781 * 2
def baseEnd_1064781 : Nat := 364496296516735848760445

theorem tailTrace_1064781 : CollatzResearch.WordTrace tailWord_1064781 prefixEnd_1064781 364496296516735848760445 := by
  unfold tailWord_1064781
  simp only [CollatzResearch.WordTrace]
  refine ⟨38835753555487761962082197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25890502370325174641388131 38835753555487761962082197)
  ·
    refine ⟨1820425947913488841972603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 38835753555487761962082197 1820425947913488841972603)
    ·
      refine ⟨2730638921870233262958905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1820425947913488841972603 2730638921870233262958905)
      ·
        refine ⟨2047979191402674947219179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2730638921870233262958905 2047979191402674947219179)
        ·
          refine ⟨3071968787104012420828769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2047979191402674947219179 3071968787104012420828769)
          ·
            refine ⟨2303976590328009315621577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3071968787104012420828769 2303976590328009315621577)
            ·
              refine ⟨1727982442746006986716183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2303976590328009315621577 1727982442746006986716183)
              ·
                refine ⟨2591973664119010480074275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1727982442746006986716183 2591973664119010480074275)
                ·
                  refine ⟨3887960496178515720111413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2591973664119010480074275 3887960496178515720111413)
                  ·
                    refine ⟨364496296516735848760445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3887960496178515720111413 364496296516735848760445)
                    ·
                      rfl

theorem cell22_1064781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_1064781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1064781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1064781 prefixEnd_1064781 := by exact prefixLift 1064781
  have htrace : WordTrace (prefixWord ++ tailWord_1064781) baseStart_1064781 baseEnd_1064781 := by
    simpa [prefixWord, tailWord_1064781, baseEnd_1064781] using wordTrace_append hprefix tailTrace_1064781
  have hstable : (prefixWord ++ tailWord_1064781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064781).length < 2 ^ (prefixWord ++ tailWord_1064781).sum := by decide
  have hdescent : baseEnd_1064781 < baseStart_1064781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064826 : List Nat := [3, 1, 1, 1, 1, 1, 6, 4, 1, 3]
def baseStart_1064826 : Nat := 118140960795 + 1064826 * 2 ^ 59
def prefixEnd_1064826 : Nat := 4983230072969 + 3 ^ 40 * 1064826 * 2
def baseEnd_1064826 : Nat := 364511700936370731385307

theorem tailTrace_1064826 : CollatzResearch.WordTrace tailWord_1064826 prefixEnd_1064826 364511700936370731385307 := by
  unfold tailWord_1064826
  simp only [CollatzResearch.WordTrace]
  refine ⟨9709348710081183661867583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25891596560216489764980221 9709348710081183661867583)
  ·
    refine ⟨14564023065121775492801375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9709348710081183661867583 14564023065121775492801375)
    ·
      refine ⟨21846034597682663239202063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14564023065121775492801375 21846034597682663239202063)
      ·
        refine ⟨32769051896523994858803095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21846034597682663239202063 32769051896523994858803095)
        ·
          refine ⟨49153577844785992288204643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32769051896523994858803095 49153577844785992288204643)
          ·
            refine ⟨73730366767178988432306965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49153577844785992288204643 73730366767178988432306965)
            ·
              refine ⟨3456110942211515082764389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 73730366767178988432306965 3456110942211515082764389)
              ·
                refine ⟨648020801664659078018323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3456110942211515082764389 648020801664659078018323)
                ·
                  refine ⟨972031202496988617027485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 648020801664659078018323 972031202496988617027485)
                  ·
                    refine ⟨364511700936370731385307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 972031202496988617027485 364511700936370731385307)
                    ·
                      rfl

theorem cell22_1064826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 4, 1, 3].length) (baseStart_1064826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1064826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1064826 prefixEnd_1064826 := by exact prefixLift 1064826
  have htrace : WordTrace (prefixWord ++ tailWord_1064826) baseStart_1064826 baseEnd_1064826 := by
    simpa [prefixWord, tailWord_1064826, baseEnd_1064826] using wordTrace_append hprefix tailTrace_1064826
  have hstable : (prefixWord ++ tailWord_1064826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064826).length < 2 ^ (prefixWord ++ tailWord_1064826).sum := by decide
  have hdescent : baseEnd_1064826 < baseStart_1064826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064837 : List Nat := [1, 3, 1, 1, 3, 2, 1, 3, 2, 5]
def baseStart_1064837 : Nat := 118140960795 + 1064837 * 2 ^ 59
def prefixEnd_1064837 : Nat := 4983230072969 + 3 ^ 40 * 1064837 * 2
def baseEnd_1064837 : Nat := 364515466461170369360273

theorem tailTrace_1064837 : CollatzResearch.WordTrace tailWord_1064837 prefixEnd_1064837 364515466461170369360273 := by
  unfold tailWord_1064837
  simp only [CollatzResearch.WordTrace]
  refine ⟨38837796043284883526120765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25891864028856589017413843 38837796043284883526120765)
  ·
    refine ⟨14564173516231831322295287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38837796043284883526120765 14564173516231831322295287)
    ·
      refine ⟨21846260274347746983442931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14564173516231831322295287 21846260274347746983442931)
      ·
        refine ⟨32769390411521620475164397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21846260274347746983442931 32769390411521620475164397)
        ·
          refine ⟨12288521404320607678186649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32769390411521620475164397 12288521404320607678186649)
          ·
            refine ⟨9216391053240455758639987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12288521404320607678186649 9216391053240455758639987)
            ·
              refine ⟨13824586579860683637959981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9216391053240455758639987 13824586579860683637959981)
              ·
                refine ⟨5184219967447756364234993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13824586579860683637959981 5184219967447756364234993)
                ·
                  refine ⟨3888164975585817273176245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5184219967447756364234993 3888164975585817273176245)
                  ·
                    refine ⟨364515466461170369360273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3888164975585817273176245 364515466461170369360273)
                    ·
                      rfl

theorem cell22_1064837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_1064837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1064837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1064837 prefixEnd_1064837 := by exact prefixLift 1064837
  have htrace : WordTrace (prefixWord ++ tailWord_1064837) baseStart_1064837 baseEnd_1064837 := by
    simpa [prefixWord, tailWord_1064837, baseEnd_1064837] using wordTrace_append hprefix tailTrace_1064837
  have hstable : (prefixWord ++ tailWord_1064837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064837).length < 2 ^ (prefixWord ++ tailWord_1064837).sum := by decide
  have hdescent : baseEnd_1064837 < baseStart_1064837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064860 : List Nat := [2, 2, 3, 3, 1, 3, 1, 3, 1, 3]
def baseStart_1064860 : Nat := 118140960795 + 1064860 * 2 ^ 59
def prefixEnd_1064860 : Nat := 4983230072969 + 3 ^ 40 * 1064860 * 2
def baseEnd_1064860 : Nat := 364523339831205976035203

theorem tailTrace_1064860 : CollatzResearch.WordTrace tailWord_1064860 prefixEnd_1064860 364523339831205976035203 := by
  unfold tailWord_1064860
  simp only [CollatzResearch.WordTrace]
  refine ⟨19419317461100779227104017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25892423281467705636138689 19419317461100779227104017)
  ·
    refine ⟨14564488095825584420328013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19419317461100779227104017 14564488095825584420328013)
    ·
      refine ⟨5461683035934594157623005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14564488095825584420328013 5461683035934594157623005)
      ·
        refine ⟨2048131138475472809108627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5461683035934594157623005 2048131138475472809108627)
        ·
          refine ⟨3072196707713209213662941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2048131138475472809108627 3072196707713209213662941)
          ·
            refine ⟨1152073765392453455123603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3072196707713209213662941 1152073765392453455123603)
            ·
              refine ⟨1728110648088680182685405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1152073765392453455123603 1728110648088680182685405)
              ·
                refine ⟨648041493033255068507027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1728110648088680182685405 648041493033255068507027)
                ·
                  refine ⟨972062239549882602760541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 648041493033255068507027 972062239549882602760541)
                  ·
                    refine ⟨364523339831205976035203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 972062239549882602760541 364523339831205976035203)
                    ·
                      rfl

theorem cell22_1064860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_1064860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1064860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1064860 prefixEnd_1064860 := by exact prefixLift 1064860
  have htrace : WordTrace (prefixWord ++ tailWord_1064860) baseStart_1064860 baseEnd_1064860 := by
    simpa [prefixWord, tailWord_1064860, baseEnd_1064860] using wordTrace_append hprefix tailTrace_1064860
  have hstable : (prefixWord ++ tailWord_1064860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064860).length < 2 ^ (prefixWord ++ tailWord_1064860).sum := by decide
  have hdescent : baseEnd_1064860 < baseStart_1064860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064912 : List Nat := [2, 1, 1, 1, 1, 2, 6, 8]
def baseStart_1064912 : Nat := 118140960795 + 1064912 * 2 ^ 59
def prefixEnd_1064912 : Nat := 4983230072969 + 3 ^ 40 * 1064912 * 2
def baseEnd_1064912 : Nat := 40504571165988352637227

theorem tailTrace_1064912 : CollatzResearch.WordTrace tailWord_1064912 prefixEnd_1064912 40504571165988352637227 := by
  unfold tailWord_1064912
  simp only [CollatzResearch.WordTrace]
  refine ⟨19420265759006585667550495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25893687678675447556733993 19420265759006585667550495)
  ·
    refine ⟨29130398638509878501325743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19420265759006585667550495 29130398638509878501325743)
    ·
      refine ⟨43695597957764817751988615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29130398638509878501325743 43695597957764817751988615)
      ·
        refine ⟨65543396936647226627982923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43695597957764817751988615 65543396936647226627982923)
        ·
          refine ⟨98315095404970839941974385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65543396936647226627982923 98315095404970839941974385)
          ·
            refine ⟨73736321553728129956480789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98315095404970839941974385 73736321553728129956480789)
            ·
              refine ⟨3456390072831006091710037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 73736321553728129956480789 3456390072831006091710037)
              ·
                refine ⟨40504571165988352637227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3456390072831006091710037 40504571165988352637227)
                ·
                  rfl

theorem cell22_1064912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 8].length) (baseStart_1064912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1064912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1064912 prefixEnd_1064912 := by exact prefixLift 1064912
  have htrace : WordTrace (prefixWord ++ tailWord_1064912) baseStart_1064912 baseEnd_1064912 := by
    simpa [prefixWord, tailWord_1064912, baseEnd_1064912] using wordTrace_append hprefix tailTrace_1064912
  have hstable : (prefixWord ++ tailWord_1064912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064912).length < 2 ^ (prefixWord ++ tailWord_1064912).sum := by decide
  have hdescent : baseEnd_1064912 < baseStart_1064912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064935 : List Nat := [1, 1, 5, 2, 3, 2, 2, 2, 4]
def baseStart_1064935 : Nat := 118140960795 + 1064935 * 2 ^ 59
def prefixEnd_1064935 : Nat := 4983230072969 + 3 ^ 40 * 1064935 * 2
def baseEnd_1064935 : Nat := 121516337954643593469991

theorem tailTrace_1064935 : CollatzResearch.WordTrace tailWord_1064935 prefixEnd_1064935 121516337954643593469991 := by
  unfold tailWord_1064935
  simp only [CollatzResearch.WordTrace]
  refine ⟨38841370396929846263188259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25894246931286564175458839 38841370396929846263188259)
  ·
    refine ⟨58262055595394769394782389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38841370396929846263188259 58262055595394769394782389)
    ·
      refine ⟨5462067712068259630760849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58262055595394769394782389 5462067712068259630760849)
      ·
        refine ⟨4096550784051194723070637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5462067712068259630760849 4096550784051194723070637)
        ·
          refine ⟨1536206544019198021151489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4096550784051194723070637 1536206544019198021151489)
          ·
            refine ⟨1152154908014398515863617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1536206544019198021151489 1152154908014398515863617)
            ·
              refine ⟨864116181010798886897713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1152154908014398515863617 864116181010798886897713)
              ·
                refine ⟨648087135758099165173285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 864116181010798886897713 648087135758099165173285)
                ·
                  refine ⟨121516337954643593469991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 648087135758099165173285 121516337954643593469991)
                  ·
                    rfl

theorem cell22_1064935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 2, 4].length) (baseStart_1064935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1064935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1064935 prefixEnd_1064935 := by exact prefixLift 1064935
  have htrace : WordTrace (prefixWord ++ tailWord_1064935) baseStart_1064935 baseEnd_1064935 := by
    simpa [prefixWord, tailWord_1064935, baseEnd_1064935] using wordTrace_append hprefix tailTrace_1064935
  have hstable : (prefixWord ++ tailWord_1064935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064935).length < 2 ^ (prefixWord ++ tailWord_1064935).sum := by decide
  have hdescent : baseEnd_1064935 < baseStart_1064935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064961 : List Nat := [1, 2, 4, 1, 2, 1, 3, 2, 3, 3]
def baseStart_1064961 : Nat := 118140960795 + 1064961 * 2 ^ 59
def prefixEnd_1064961 : Nat := 4983230072969 + 3 ^ 40 * 1064961 * 2
def baseEnd_1064961 : Nat := 364557914195275379259893

theorem tailTrace_1064961 : CollatzResearch.WordTrace tailWord_1064961 prefixEnd_1064961 364557914195275379259893 := by
  unfold tailWord_1064961
  simp only [CollatzResearch.WordTrace]
  refine ⟨38842318694835652703634737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25894879129890435135756491 38842318694835652703634737)
  ·
    refine ⟨29131739021126739527726053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38842318694835652703634737 29131739021126739527726053)
    ·
      refine ⟨5462201066461263661448635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29131739021126739527726053 5462201066461263661448635)
      ·
        refine ⟨8193301599691895492172953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5462201066461263661448635 8193301599691895492172953)
        ·
          refine ⟨6144976199768921619129715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8193301599691895492172953 6144976199768921619129715)
          ·
            refine ⟨9217464299653382428694573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6144976199768921619129715 9217464299653382428694573)
            ·
              refine ⟨3456549112370018410760465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9217464299653382428694573 3456549112370018410760465)
              ·
                refine ⟨2592411834277513808070349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3456549112370018410760465 2592411834277513808070349)
                ·
                  refine ⟨972154437854067678026381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2592411834277513808070349 972154437854067678026381)
                  ·
                    refine ⟨364557914195275379259893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 972154437854067678026381 364557914195275379259893)
                    ·
                      rfl

theorem cell22_1064961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_1064961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1064961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1064961 prefixEnd_1064961 := by exact prefixLift 1064961
  have htrace : WordTrace (prefixWord ++ tailWord_1064961) baseStart_1064961 baseEnd_1064961 := by
    simpa [prefixWord, tailWord_1064961, baseEnd_1064961] using wordTrace_append hprefix tailTrace_1064961
  have hstable : (prefixWord ++ tailWord_1064961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064961).length < 2 ^ (prefixWord ++ tailWord_1064961).sum := by decide
  have hdescent : baseEnd_1064961 < baseStart_1064961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064974 : List Nat := [4, 1, 1, 2, 2, 1, 2, 2, 7]
def baseStart_1064974 : Nat := 118140960795 + 1064974 * 2 ^ 59
def prefixEnd_1064974 : Nat := 4983230072969 + 3 ^ 40 * 1064974 * 2
def baseEnd_1064974 : Nat := 121520788120315892894951

theorem tailTrace_1064974 : CollatzResearch.WordTrace tailWord_1064974 prefixEnd_1064974 121520788120315892894951 := by
  unfold tailWord_1064974
  simp only [CollatzResearch.WordTrace]
  refine ⟨4855349105473569490482247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25895195229192370615905317 4855349105473569490482247)
  ·
    refine ⟨7283023658210354235723371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4855349105473569490482247 7283023658210354235723371)
    ·
      refine ⟨10924535487315531353585057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7283023658210354235723371 10924535487315531353585057)
      ·
        refine ⟨8193401615486648515188793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10924535487315531353585057 8193401615486648515188793)
        ·
          refine ⟨6145051211614986386391595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8193401615486648515188793 6145051211614986386391595)
          ·
            refine ⟨9217576817422479579587393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6145051211614986386391595 9217576817422479579587393)
            ·
              refine ⟨6913182613066859684690545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9217576817422479579587393 6913182613066859684690545)
              ·
                refine ⟨5184886959800144763517909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6913182613066859684690545 5184886959800144763517909)
                ·
                  refine ⟨121520788120315892894951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5184886959800144763517909 121520788120315892894951)
                  ·
                    rfl

theorem cell22_1064974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_1064974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1064974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1064974 prefixEnd_1064974 := by exact prefixLift 1064974
  have htrace : WordTrace (prefixWord ++ tailWord_1064974) baseStart_1064974 baseEnd_1064974 := by
    simpa [prefixWord, tailWord_1064974, baseEnd_1064974] using wordTrace_append hprefix tailTrace_1064974
  have hstable : (prefixWord ++ tailWord_1064974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064974).length < 2 ^ (prefixWord ++ tailWord_1064974).sum := by decide
  have hdescent : baseEnd_1064974 < baseStart_1064974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065004 : List Nat := [2, 2, 1, 1, 1, 2, 2, 4, 3, 4]
def baseStart_1065004 : Nat := 118140960795 + 1065004 * 2 ^ 59
def prefixEnd_1065004 : Nat := 4983230072969 + 3 ^ 40 * 1065004 * 2
def baseEnd_1065004 : Nat := 364572633974037600434761

theorem tailTrace_1065004 : CollatzResearch.WordTrace tailWord_1065004 prefixEnd_1065004 364572633974037600434761 := by
  unfold tailWord_1065004
  simp only [CollatzResearch.WordTrace]
  refine ⟨19421943516839935523725033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25895924689119914031633377 19421943516839935523725033)
  ·
    refine ⟨14566457637629951642793775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19421943516839935523725033 14566457637629951642793775)
    ·
      refine ⟨21849686456444927464190663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14566457637629951642793775 21849686456444927464190663)
      ·
        refine ⟨32774529684667391196285995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21849686456444927464190663 32774529684667391196285995)
        ·
          refine ⟨49161794527001086794428993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32774529684667391196285995 49161794527001086794428993)
          ·
            refine ⟨36871345895250815095821745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49161794527001086794428993 36871345895250815095821745)
            ·
              refine ⟨27653509421438111321866309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36871345895250815095821745 27653509421438111321866309)
              ·
                refine ⟨5185033016519645872849933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27653509421438111321866309 5185033016519645872849933)
                ·
                  refine ⟨1944387381194867202318725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5185033016519645872849933 1944387381194867202318725)
                  ·
                    refine ⟨364572633974037600434761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1944387381194867202318725 364572633974037600434761)
                    ·
                      rfl

theorem cell22_1065004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 4].length) (baseStart_1065004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1065004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1065004 prefixEnd_1065004 := by exact prefixLift 1065004
  have htrace : WordTrace (prefixWord ++ tailWord_1065004) baseStart_1065004 baseEnd_1065004 := by
    simpa [prefixWord, tailWord_1065004, baseEnd_1065004] using wordTrace_append hprefix tailTrace_1065004
  have hstable : (prefixWord ++ tailWord_1065004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065004).length < 2 ^ (prefixWord ++ tailWord_1065004).sum := by decide
  have hdescent : baseEnd_1065004 < baseStart_1065004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065006 : List Nat := [4, 1, 3, 1, 1, 2, 2, 1, 2, 5]
def baseStart_1065006 : Nat := 118140960795 + 1065006 * 2 ^ 59
def prefixEnd_1065006 : Nat := 4983230072969 + 3 ^ 40 * 1065006 * 2
def baseEnd_1065006 : Nat := 364573318614910261884755

theorem tailTrace_1065006 : CollatzResearch.WordTrace tailWord_1065006 prefixEnd_1065006 364573318614910261884755 := by
  unfold tailWord_1065006
  simp only [CollatzResearch.WordTrace]
  refine ⟨4855494997459078173627859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25895973319781750259348581 4855494997459078173627859)
  ·
    refine ⟨7283242496188617260441789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4855494997459078173627859 7283242496188617260441789)
    ·
      refine ⟨2731215936070731472665671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7283242496188617260441789 2731215936070731472665671)
      ·
        refine ⟨4096823904106097208998507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2731215936070731472665671 4096823904106097208998507)
        ·
          refine ⟨6145235856159145813497761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4096823904106097208998507 6145235856159145813497761)
          ·
            refine ⟨4608926892119359360123321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6145235856159145813497761 4608926892119359360123321)
            ·
              refine ⟨3456695169089519520092491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4608926892119359360123321 3456695169089519520092491)
              ·
                refine ⟨5185042753634279280138737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3456695169089519520092491 5185042753634279280138737)
                ·
                  refine ⟨3888782065225709460104053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5185042753634279280138737 3888782065225709460104053)
                  ·
                    refine ⟨364573318614910261884755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3888782065225709460104053 364573318614910261884755)
                    ·
                      rfl

theorem cell22_1065006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_1065006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1065006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1065006 prefixEnd_1065006 := by exact prefixLift 1065006
  have htrace : WordTrace (prefixWord ++ tailWord_1065006) baseStart_1065006 baseEnd_1065006 := by
    simpa [prefixWord, tailWord_1065006, baseEnd_1065006] using wordTrace_append hprefix tailTrace_1065006
  have hstable : (prefixWord ++ tailWord_1065006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065006).length < 2 ^ (prefixWord ++ tailWord_1065006).sum := by decide
  have hdescent : baseEnd_1065006 < baseStart_1065006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065034 : List Nat := [3, 1, 2, 1, 1, 2, 1, 3, 3, 5]
def baseStart_1065034 : Nat := 118140960795 + 1065034 * 2 ^ 59
def prefixEnd_1065034 : Nat := 4983230072969 + 3 ^ 40 * 1065034 * 2
def baseEnd_1065034 : Nat := 364582903587127522184669

theorem tailTrace_1065034 : CollatzResearch.WordTrace tailWord_1065034 prefixEnd_1065034 364582903587127522184669 := by
  unfold tailWord_1065034
  simp only [CollatzResearch.WordTrace]
  refine ⟨9711245305892796542760539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25896654149047457447361437 9711245305892796542760539)
  ·
    refine ⟨14566867958839194814140809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9711245305892796542760539 14566867958839194814140809)
    ·
      refine ⟨10925150969129396110605607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14566867958839194814140809 10925150969129396110605607)
      ·
        refine ⟨16387726453694094165908411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10925150969129396110605607 16387726453694094165908411)
        ·
          refine ⟨24581589680541141248862617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16387726453694094165908411 24581589680541141248862617)
          ·
            refine ⟨18436192260405855936646963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24581589680541141248862617 18436192260405855936646963)
            ·
              refine ⟨27654288390608783904970445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18436192260405855936646963 27654288390608783904970445)
              ·
                refine ⟨10370358146478293964363917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27654288390608783904970445 10370358146478293964363917)
                ·
                  refine ⟨3888884304929360236636469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10370358146478293964363917 3888884304929360236636469)
                  ·
                    refine ⟨364582903587127522184669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3888884304929360236636469 364582903587127522184669)
                    ·
                      rfl

theorem cell22_1065034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_1065034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1065034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1065034 prefixEnd_1065034 := by exact prefixLift 1065034
  have htrace : WordTrace (prefixWord ++ tailWord_1065034) baseStart_1065034 baseEnd_1065034 := by
    simpa [prefixWord, tailWord_1065034, baseEnd_1065034] using wordTrace_append hprefix tailTrace_1065034
  have hstable : (prefixWord ++ tailWord_1065034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065034).length < 2 ^ (prefixWord ++ tailWord_1065034).sum := by decide
  have hdescent : baseEnd_1065034 < baseStart_1065034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065053 : List Nat := [1, 4, 4, 1, 1, 1, 3, 1, 6]
def baseStart_1065053 : Nat := 118140960795 + 1065053 * 2 ^ 59
def prefixEnd_1065053 : Nat := 4983230072969 + 3 ^ 40 * 1065053 * 2
def baseEnd_1065053 : Nat := 121529802558472601986537

theorem tailTrace_1065053 : CollatzResearch.WordTrace tailWord_1065053 prefixEnd_1065053 121529802558472601986537 := by
  unfold tailWord_1065053
  simp only [CollatzResearch.WordTrace]
  refine ⟨38845674210502352415983813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25897116140334901610655875 38845674210502352415983813)
  ·
    refine ⟨7283563914469191077996965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38845674210502352415983813 7283563914469191077996965)
    ·
      refine ⟨1365668233962973327124431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7283563914469191077996965 1365668233962973327124431)
      ·
        refine ⟨2048502350944459990686647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1365668233962973327124431 2048502350944459990686647)
        ·
          refine ⟨3072753526416689986029971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2048502350944459990686647 3072753526416689986029971)
          ·
            refine ⟨4609130289625034979044957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3072753526416689986029971 4609130289625034979044957)
            ·
              refine ⟨1728423858609388117141859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4609130289625034979044957 1728423858609388117141859)
              ·
                refine ⟨2592635787914082175712789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1728423858609388117141859 2592635787914082175712789)
                ·
                  refine ⟨121529802558472601986537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2592635787914082175712789 121529802558472601986537)
                  ·
                    rfl

theorem cell22_1065053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_1065053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1065053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1065053 prefixEnd_1065053 := by exact prefixLift 1065053
  have htrace : WordTrace (prefixWord ++ tailWord_1065053) baseStart_1065053 baseEnd_1065053 := by
    simpa [prefixWord, tailWord_1065053, baseEnd_1065053] using wordTrace_append hprefix tailTrace_1065053
  have hstable : (prefixWord ++ tailWord_1065053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065053).length < 2 ^ (prefixWord ++ tailWord_1065053).sum := by decide
  have hdescent : baseEnd_1065053 < baseStart_1065053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065068 : List Nat := [2, 2, 1, 1, 3, 4, 1, 3, 2, 3]
def baseStart_1065068 : Nat := 118140960795 + 1065068 * 2 ^ 59
def prefixEnd_1065068 : Nat := 4983230072969 + 3 ^ 40 * 1065068 * 2
def baseEnd_1065068 : Nat := 364594542481962766834565

theorem tailTrace_1065068 : CollatzResearch.WordTrace tailWord_1065068 prefixEnd_1065068 364594542481962766834565 := by
  unfold tailWord_1065068
  simp only [CollatzResearch.WordTrace]
  refine ⟨19423110652724004988889929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25897480870298673318519905 19423110652724004988889929)
  ·
    refine ⟨14567332989543003741667447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19423110652724004988889929 14567332989543003741667447)
    ·
      refine ⟨21850999484314505612501171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14567332989543003741667447 21850999484314505612501171)
      ·
        refine ⟨32776499226471758418751757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21850999484314505612501171 32776499226471758418751757)
        ·
          refine ⟨12291187209926909407031909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32776499226471758418751757 12291187209926909407031909)
          ·
            refine ⟨2304597601861295513818483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12291187209926909407031909 2304597601861295513818483)
            ·
              refine ⟨3456896402791943270727725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2304597601861295513818483 3456896402791943270727725)
              ·
                refine ⟨1296336151046978726522897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3456896402791943270727725 1296336151046978726522897)
                ·
                  refine ⟨972252113285234044892173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1296336151046978726522897 972252113285234044892173)
                  ·
                    refine ⟨364594542481962766834565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 972252113285234044892173 364594542481962766834565)
                    ·
                      rfl

theorem cell22_1065068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 3].length) (baseStart_1065068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1065068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1065068 prefixEnd_1065068 := by exact prefixLift 1065068
  have htrace : WordTrace (prefixWord ++ tailWord_1065068) baseStart_1065068 baseEnd_1065068 := by
    simpa [prefixWord, tailWord_1065068, baseEnd_1065068] using wordTrace_append hprefix tailTrace_1065068
  have hstable : (prefixWord ++ tailWord_1065068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065068).length < 2 ^ (prefixWord ++ tailWord_1065068).sum := by decide
  have hdescent : baseEnd_1065068 < baseStart_1065068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065134 : List Nat := [4, 1, 4, 2, 2, 1, 1, 1, 2, 4]
def baseStart_1065134 : Nat := 118140960795 + 1065134 * 2 ^ 59
def prefixEnd_1065134 : Nat := 4983230072969 + 3 ^ 40 * 1065134 * 2
def baseEnd_1065134 : Nat := 364617135630760594684363

theorem tailTrace_1065134 : CollatzResearch.WordTrace tailWord_1065134 prefixEnd_1065134 364617135630760594684363 := by
  unfold tailWord_1065134
  simp only [CollatzResearch.WordTrace]
  refine ⟨4856078565401112906210307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25899085682139268833121637 4856078565401112906210307)
  ·
    refine ⟨7284117848101669359315461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4856078565401112906210307 7284117848101669359315461)
    ·
      refine ⟨1365772096519063004871649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7284117848101669359315461 1365772096519063004871649)
      ·
        refine ⟨1024329072389297253653737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1365772096519063004871649 1024329072389297253653737)
        ·
          refine ⟨768246804291972940240303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1024329072389297253653737 768246804291972940240303)
          ·
            refine ⟨1152370206437959410360455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 768246804291972940240303 1152370206437959410360455)
            ·
              refine ⟨1728555309656939115540683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1152370206437959410360455 1728555309656939115540683)
              ·
                refine ⟨2592832964485408673311025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1728555309656939115540683 2592832964485408673311025)
                ·
                  refine ⟨1944624723364056504983269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2592832964485408673311025 1944624723364056504983269)
                  ·
                    refine ⟨364617135630760594684363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1944624723364056504983269 364617135630760594684363)
                    ·
                      rfl

theorem cell22_1065134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_1065134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1065134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1065134 prefixEnd_1065134 := by exact prefixLift 1065134
  have htrace : WordTrace (prefixWord ++ tailWord_1065134) baseStart_1065134 baseEnd_1065134 := by
    simpa [prefixWord, tailWord_1065134, baseEnd_1065134] using wordTrace_append hprefix tailTrace_1065134
  have hstable : (prefixWord ++ tailWord_1065134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065134).length < 2 ^ (prefixWord ++ tailWord_1065134).sum := by decide
  have hdescent : baseEnd_1065134 < baseStart_1065134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065201 : List Nat := [1, 2, 2, 2, 2, 1, 4, 1, 1, 6]
def baseStart_1065201 : Nat := 118140960795 + 1065201 * 2 ^ 59
def prefixEnd_1065201 : Nat := 4983230072969 + 3 ^ 40 * 1065201 * 2
def baseEnd_1065201 : Nat := 364640071099994753259157

theorem tailTrace_1065201 : CollatzResearch.WordTrace tailWord_1065201 prefixEnd_1065201 364640071099994753259157 := by
  unfold tailWord_1065201
  simp only [CollatzResearch.WordTrace]
  refine ⟨38851072213966173692371457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25900714809310782461580971 38851072213966173692371457)
  ·
    refine ⟨29138304160474630269278593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38851072213966173692371457 29138304160474630269278593)
    ·
      refine ⟨21853728120355972701958945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29138304160474630269278593 21853728120355972701958945)
      ·
        refine ⟨16390296090266979526469209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21853728120355972701958945 16390296090266979526469209)
        ·
          refine ⟨12292722067700234644851907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16390296090266979526469209 12292722067700234644851907)
          ·
            refine ⟨18439083101550351967277861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12292722067700234644851907 18439083101550351967277861)
            ·
              refine ⟨3457328081540690993864599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18439083101550351967277861 3457328081540690993864599)
              ·
                refine ⟨5185992122311036490796899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3457328081540690993864599 5185992122311036490796899)
                ·
                  refine ⟨7778988183466554736195349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5185992122311036490796899 7778988183466554736195349)
                  ·
                    refine ⟨364640071099994753259157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7778988183466554736195349 364640071099994753259157)
                    ·
                      rfl

theorem cell22_1065201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 6].length) (baseStart_1065201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1065201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1065201 prefixEnd_1065201 := by exact prefixLift 1065201
  have htrace : WordTrace (prefixWord ++ tailWord_1065201) baseStart_1065201 baseEnd_1065201 := by
    simpa [prefixWord, tailWord_1065201, baseEnd_1065201] using wordTrace_append hprefix tailTrace_1065201
  have hstable : (prefixWord ++ tailWord_1065201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065201).length < 2 ^ (prefixWord ++ tailWord_1065201).sum := by decide
  have hdescent : baseEnd_1065201 < baseStart_1065201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065325 : List Nat := [1, 5, 1, 1, 1, 2, 3, 3, 1, 4]
def baseStart_1065325 : Nat := 118140960795 + 1065325 * 2 ^ 59
def prefixEnd_1065325 : Nat := 4983230072969 + 3 ^ 40 * 1065325 * 2
def baseEnd_1065325 : Nat := 364682518834099763158777

theorem tailTrace_1065325 : CollatzResearch.WordTrace tailWord_1065325 prefixEnd_1065325 364682518834099763158777 := by
  unfold tailWord_1065325
  simp only [CollatzResearch.WordTrace]
  refine ⟨38855594865516942869885429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25903729910344628579923619 38855594865516942869885429)
  ·
    refine ⟨3642712018642213394051759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38855594865516942869885429 3642712018642213394051759)
    ·
      refine ⟨5464068027963320091077639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3642712018642213394051759 5464068027963320091077639)
      ·
        refine ⟨8196102041944980136616459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5464068027963320091077639 8196102041944980136616459)
        ·
          refine ⟨12294153062917470204924689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8196102041944980136616459 12294153062917470204924689)
          ·
            refine ⟨9220614797188102653693517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12294153062917470204924689 9220614797188102653693517)
            ·
              refine ⟨3457730548945538495135069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9220614797188102653693517 3457730548945538495135069)
              ·
                refine ⟨1296648955854576935675651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3457730548945538495135069 1296648955854576935675651)
                ·
                  refine ⟨1944973433781865403513477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1296648955854576935675651 1944973433781865403513477)
                  ·
                    refine ⟨364682518834099763158777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1944973433781865403513477 364682518834099763158777)
                    ·
                      rfl

theorem cell22_1065325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_1065325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1065325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1065325 prefixEnd_1065325 := by exact prefixLift 1065325
  have htrace : WordTrace (prefixWord ++ tailWord_1065325) baseStart_1065325 baseEnd_1065325 := by
    simpa [prefixWord, tailWord_1065325, baseEnd_1065325] using wordTrace_append hprefix tailTrace_1065325
  have hstable : (prefixWord ++ tailWord_1065325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065325).length < 2 ^ (prefixWord ++ tailWord_1065325).sum := by decide
  have hdescent : baseEnd_1065325 < baseStart_1065325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
