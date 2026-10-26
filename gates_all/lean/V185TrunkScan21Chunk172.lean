import V185TrunkScan21Chunk171

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_2094826 : List Nat := [3, 1, 3, 1, 1, 1, 6, 2, 3]
def baseStart_2094826 : Nat := 118140960795 + 2094826 * 2 ^ 59
def prefixEnd_2094826 : Nat := 4983230072969 + 3 ^ 40 * 2094826 * 2
def baseEnd_2094826 : Nat := 478067833571344985484923

theorem tailTrace_2094826 : CollatzResearch.WordTrace tailWord_2094826 prefixEnd_2094826 478067833571344985484923 := by
  unfold tailWord_2094826
  simp only [CollatzResearch.WordTrace]
  refine ⟨19101145277202661160640083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50936387405873763095040221 19101145277202661160640083)
  ·
    refine ⟨28651717915803991740960125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19101145277202661160640083 28651717915803991740960125)
    ·
      refine ⟨10744394218426496902860047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28651717915803991740960125 10744394218426496902860047)
      ·
        refine ⟨16116591327639745354290071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10744394218426496902860047 16116591327639745354290071)
        ·
          refine ⟨24174886991459618031435107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16116591327639745354290071 24174886991459618031435107)
          ·
            refine ⟨36262330487189427047152661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24174886991459618031435107 36262330487189427047152661)
            ·
              refine ⟨1699796741587004392835281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36262330487189427047152661 1699796741587004392835281)
              ·
                refine ⟨1274847556190253294626461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1699796741587004392835281 1274847556190253294626461)
                ·
                  refine ⟨478067833571344985484923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1274847556190253294626461 478067833571344985484923)
                  ·
                    rfl

theorem cell21_2094826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 2, 3].length) (baseStart_2094826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2094826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2094826 prefixEnd_2094826 := by exact prefixLift 2094826
  have htrace : WordTrace (prefixWord ++ tailWord_2094826) baseStart_2094826 baseEnd_2094826 := by
    simpa [prefixWord, tailWord_2094826, baseEnd_2094826] using wordTrace_append hprefix tailTrace_2094826
  have hstable : (prefixWord ++ tailWord_2094826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094826).length < 2 ^ (prefixWord ++ tailWord_2094826).sum := by decide
  have hdescent : baseEnd_2094826 < baseStart_2094826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094851 : List Nat := [1, 1, 1, 3, 2, 2, 3, 1, 7]
def baseStart_2094851 : Nat := 118140960795 + 2094851 * 2 ^ 59
def prefixEnd_2094851 : Nat := 4983230072969 + 3 ^ 40 * 2094851 * 2
def baseEnd_2094851 : Nat := 478073538911950497568205

theorem tailTrace_2094851 : CollatzResearch.WordTrace tailWord_2094851 prefixEnd_2094851 478073538911950497568205 := by
  unfold tailWord_2094851
  simp only [CollatzResearch.WordTrace]
  refine ⟨76405492933720073912220407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50936995289146715941480271 76405492933720073912220407)
  ·
    refine ⟨114608239400580110868330611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76405492933720073912220407 114608239400580110868330611)
    ·
      refine ⟨171912359100870166302495917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114608239400580110868330611 171912359100870166302495917)
      ·
        refine ⟨64467134662826312363435969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171912359100870166302495917 64467134662826312363435969)
        ·
          refine ⟨48350350997119734272576977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64467134662826312363435969 48350350997119734272576977)
          ·
            refine ⟨36262763247839800704432733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48350350997119734272576977 36262763247839800704432733)
            ·
              refine ⟨13598536217939925264162275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36262763247839800704432733 13598536217939925264162275)
              ·
                refine ⟨20397804326909887896243413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13598536217939925264162275 20397804326909887896243413)
                ·
                  refine ⟨478073538911950497568205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20397804326909887896243413 478073538911950497568205)
                  ·
                    rfl

theorem cell21_2094851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 7].length) (baseStart_2094851 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2094851 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2094851 prefixEnd_2094851 := by exact prefixLift 2094851
  have htrace : WordTrace (prefixWord ++ tailWord_2094851) baseStart_2094851 baseEnd_2094851 := by
    simpa [prefixWord, tailWord_2094851, baseEnd_2094851] using wordTrace_append hprefix tailTrace_2094851
  have hstable : (prefixWord ++ tailWord_2094851).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094851).length < 2 ^ (prefixWord ++ tailWord_2094851).sum := by decide
  have hdescent : baseEnd_2094851 < baseStart_2094851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094885 : List Nat := [1, 3, 1, 2, 3, 2, 2, 4, 3]
def baseStart_2094885 : Nat := 118140960795 + 2094885 * 2 ^ 59
def prefixEnd_2094885 : Nat := 4983230072969 + 3 ^ 40 * 2094885 * 2
def baseEnd_2094885 : Nat := 478081298175173994001469

theorem tailTrace_2094885 : CollatzResearch.WordTrace tailWord_2094885 prefixEnd_2094885 478081298175173994001469 := by
  unfold tailWord_2094885
  simp only [CollatzResearch.WordTrace]
  refine ⟨76406733015596897718958109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50937822010397931812638739 76406733015596897718958109)
  ·
    refine ⟨28652524880848836644609291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76406733015596897718958109 28652524880848836644609291)
    ·
      refine ⟨42978787321273254966913937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28652524880848836644609291 42978787321273254966913937)
      ·
        refine ⟨32234090490954941225185453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42978787321273254966913937 32234090490954941225185453)
        ·
          refine ⟨12087783934108102959444545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32234090490954941225185453 12087783934108102959444545)
          ·
            refine ⟨9065837950581077219583409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12087783934108102959444545 9065837950581077219583409)
            ·
              refine ⟨6799378462935807914687557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9065837950581077219583409 6799378462935807914687557)
              ·
                refine ⟨1274883461800463984003917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6799378462935807914687557 1274883461800463984003917)
                ·
                  refine ⟨478081298175173994001469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1274883461800463984003917 478081298175173994001469)
                  ·
                    rfl

theorem cell21_2094885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 4, 3].length) (baseStart_2094885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2094885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2094885 prefixEnd_2094885 := by exact prefixLift 2094885
  have htrace : WordTrace (prefixWord ++ tailWord_2094885) baseStart_2094885 baseEnd_2094885 := by
    simpa [prefixWord, tailWord_2094885, baseEnd_2094885] using wordTrace_append hprefix tailTrace_2094885
  have hstable : (prefixWord ++ tailWord_2094885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094885).length < 2 ^ (prefixWord ++ tailWord_2094885).sum := by decide
  have hdescent : baseEnd_2094885 < baseStart_2094885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094944 : List Nat := [2, 1, 1, 3, 3, 2, 3, 1, 5]
def baseStart_2094944 : Nat := 118140960795 + 2094944 * 2 ^ 59
def prefixEnd_2094944 : Nat := 4983230072969 + 3 ^ 40 * 2094944 * 2
def baseEnd_2094944 : Nat := 478094762779003002518015

theorem tailTrace_2094944 : CollatzResearch.WordTrace tailWord_2094944 prefixEnd_2094944 478094762779003002518015 := by
  unfold tailWord_2094944
  simp only [CollatzResearch.WordTrace]
  refine ⟨38204442461191575397677943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50939256614922100530237257 38204442461191575397677943)
  ·
    refine ⟨57306663691787363096516915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38204442461191575397677943 57306663691787363096516915)
    ·
      refine ⟨85959995537681044644775373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57306663691787363096516915 85959995537681044644775373)
      ·
        refine ⟨32234998326630391741790765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85959995537681044644775373 32234998326630391741790765)
        ·
          refine ⟨12088124372486396903171537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32234998326630391741790765 12088124372486396903171537)
          ·
            refine ⟨9066093279364797677378653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12088124372486396903171537 9066093279364797677378653)
            ·
              refine ⟨3399784979761799129016995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9066093279364797677378653 3399784979761799129016995)
              ·
                refine ⟨5099677469642698693525493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3399784979761799129016995 5099677469642698693525493)
                ·
                  refine ⟨478094762779003002518015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5099677469642698693525493 478094762779003002518015)
                  ·
                    rfl

theorem cell21_2094944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 5].length) (baseStart_2094944 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2094944 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2094944 prefixEnd_2094944 := by exact prefixLift 2094944
  have htrace : WordTrace (prefixWord ++ tailWord_2094944) baseStart_2094944 baseEnd_2094944 := by
    simpa [prefixWord, tailWord_2094944, baseEnd_2094944] using wordTrace_append hprefix tailTrace_2094944
  have hstable : (prefixWord ++ tailWord_2094944).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094944).length < 2 ^ (prefixWord ++ tailWord_2094944).sum := by decide
  have hdescent : baseEnd_2094944 < baseStart_2094944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095037 : List Nat := [1, 4, 1, 2, 3, 1, 1, 5, 3]
def baseStart_2095037 : Nat := 118140960795 + 2095037 * 2 ^ 59
def prefixEnd_2095037 : Nat := 4983230072969 + 3 ^ 40 * 2095037 * 2
def baseEnd_2095037 : Nat := 478115986646055507467825

theorem tailTrace_2095037 : CollatzResearch.WordTrace tailWord_2095037 prefixEnd_2095037 478115986646055507467825 := by
  unfold tailWord_2095037
  simp only [CollatzResearch.WordTrace]
  refine ⟨76412276911046227678491365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50941517940697485118994243 76412276911046227678491365)
  ·
    refine ⟨14327301920821167689717131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76412276911046227678491365 14327301920821167689717131)
    ·
      refine ⟨21490952881231751534575697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14327301920821167689717131 21490952881231751534575697)
      ·
        refine ⟨16118214660923813650931773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21490952881231751534575697 16118214660923813650931773)
        ·
          refine ⟨6044330497846430119099415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16118214660923813650931773 6044330497846430119099415)
          ·
            refine ⟨9066495746769645178649123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6044330497846430119099415 9066495746769645178649123)
            ·
              refine ⟨13599743620154467767973685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9066495746769645178649123 13599743620154467767973685)
              ·
                refine ⟨1274975964389481353247533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13599743620154467767973685 1274975964389481353247533)
                ·
                  refine ⟨478115986646055507467825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1274975964389481353247533 478115986646055507467825)
                  ·
                    rfl

theorem cell21_2095037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 5, 3].length) (baseStart_2095037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2095037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2095037 prefixEnd_2095037 := by exact prefixLift 2095037
  have htrace : WordTrace (prefixWord ++ tailWord_2095037) baseStart_2095037 baseEnd_2095037 := by
    simpa [prefixWord, tailWord_2095037, baseEnd_2095037] using wordTrace_append hprefix tailTrace_2095037
  have hstable : (prefixWord ++ tailWord_2095037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095037).length < 2 ^ (prefixWord ++ tailWord_2095037).sum := by decide
  have hdescent : baseEnd_2095037 < baseStart_2095037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095265 : List Nat := [1, 2, 3, 3, 1, 2, 3, 3, 3]
def baseStart_2095265 : Nat := 118140960795 + 2095265 * 2 ^ 59
def prefixEnd_2095265 : Nat := 4983230072969 + 3 ^ 40 * 2095265 * 2
def baseEnd_2095265 : Nat := 478168019352377777667359

theorem tailTrace_2095265 : CollatzResearch.WordTrace tailWord_2095265 prefixEnd_2095265 478168019352377777667359 := by
  unfold tailWord_2095265
  simp only [CollatzResearch.WordTrace]
  refine ⟨76420592754220222617791249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50947061836146815078527499 76420592754220222617791249)
  ·
    refine ⟨57315444565665166963343437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76420592754220222617791249 57315444565665166963343437)
    ·
      refine ⟨21493291712124437611253789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57315444565665166963343437 21493291712124437611253789)
      ·
        refine ⟨8059984392046664104220171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21493291712124437611253789 8059984392046664104220171)
        ·
          refine ⟨12089976588069996156330257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8059984392046664104220171 12089976588069996156330257)
          ·
            refine ⟨9067482441052497117247693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12089976588069996156330257 9067482441052497117247693)
            ·
              refine ⟨3400305915394686418967885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9067482441052497117247693 3400305915394686418967885)
              ·
                refine ⟨1275114718273007407112957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3400305915394686418967885 1275114718273007407112957)
                ·
                  refine ⟨478168019352377777667359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1275114718273007407112957 478168019352377777667359)
                  ·
                    rfl

theorem cell21_2095265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 3, 3].length) (baseStart_2095265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2095265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2095265 prefixEnd_2095265 := by exact prefixLift 2095265
  have htrace : WordTrace (prefixWord ++ tailWord_2095265) baseStart_2095265 baseEnd_2095265 := by
    simpa [prefixWord, tailWord_2095265, baseEnd_2095265] using wordTrace_append hprefix tailTrace_2095265
  have hstable : (prefixWord ++ tailWord_2095265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095265).length < 2 ^ (prefixWord ++ tailWord_2095265).sum := by decide
  have hdescent : baseEnd_2095265 < baseStart_2095265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095296 : List Nat := [2, 1, 1, 2, 5, 3, 2, 1, 4]
def baseStart_2095296 : Nat := 118140960795 + 2095296 * 2 ^ 59
def prefixEnd_2095296 : Nat := 4983230072969 + 3 ^ 40 * 2095296 * 2
def baseEnd_2095296 : Nat := 478175093974728612650629

theorem tailTrace_2095296 : CollatzResearch.WordTrace tailWord_2095296 prefixEnd_2095296 478175093974728612650629 := by
  unfold tailWord_2095296
  simp only [CollatzResearch.WordTrace]
  refine ⟨38210861708553957456084871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50947815611405276608113161 38210861708553957456084871)
  ·
    refine ⟨57316292562830936184127307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38210861708553957456084871 57316292562830936184127307)
    ·
      refine ⟨85974438844246404276190961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57316292562830936184127307 85974438844246404276190961)
      ·
        refine ⟨64480829133184803207143221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85974438844246404276190961 64480829133184803207143221)
        ·
          refine ⟨6045077731236075300669677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64480829133184803207143221 6045077731236075300669677)
          ·
            refine ⟨2266904149213528237751129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6045077731236075300669677 2266904149213528237751129)
            ·
              refine ⟨1700178111910146178313347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2266904149213528237751129 1700178111910146178313347)
              ·
                refine ⟨2550267167865219267470021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1700178111910146178313347 2550267167865219267470021)
                ·
                  refine ⟨478175093974728612650629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2550267167865219267470021 478175093974728612650629)
                  ·
                    rfl

theorem cell21_2095296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 1, 4].length) (baseStart_2095296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2095296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2095296 prefixEnd_2095296 := by exact prefixLift 2095296
  have htrace : WordTrace (prefixWord ++ tailWord_2095296) baseStart_2095296 baseEnd_2095296 := by
    simpa [prefixWord, tailWord_2095296, baseEnd_2095296] using wordTrace_append hprefix tailTrace_2095296
  have hstable : (prefixWord ++ tailWord_2095296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095296).length < 2 ^ (prefixWord ++ tailWord_2095296).sum := by decide
  have hdescent : baseEnd_2095296 < baseStart_2095296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095321 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 8]
def baseStart_2095321 : Nat := 118140960795 + 2095321 * 2 ^ 59
def prefixEnd_2095321 : Nat := 4983230072969 + 3 ^ 40 * 2095321 * 2
def baseEnd_2095321 : Nat := 478180799315334124733911

theorem tailTrace_2095321 : CollatzResearch.WordTrace tailWord_2095321 prefixEnd_2095321 478180799315334124733911 := by
  unfold tailWord_2095321
  simp only [CollatzResearch.WordTrace]
  refine ⟨76422635242017344181829817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50948423494678229454553211 76422635242017344181829817)
  ·
    refine ⟨57316976431513008136372363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76422635242017344181829817 57316976431513008136372363)
    ·
      refine ⟨85975464647269512204558545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57316976431513008136372363 85975464647269512204558545)
      ·
        refine ⟨64481598485452134153418909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85975464647269512204558545 64481598485452134153418909)
        ·
          refine ⟨24180599432044550307532091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64481598485452134153418909 24180599432044550307532091)
          ·
            refine ⟨36270899148066825461298137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24180599432044550307532091 36270899148066825461298137)
            ·
              refine ⟨27203174361050119095973603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36270899148066825461298137 27203174361050119095973603)
              ·
                refine ⟨40804761541575178643960405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27203174361050119095973603 40804761541575178643960405)
                ·
                  refine ⟨478180799315334124733911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40804761541575178643960405 478180799315334124733911)
                  ·
                    rfl

theorem cell21_2095321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 8].length) (baseStart_2095321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2095321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2095321 prefixEnd_2095321 := by exact prefixLift 2095321
  have htrace : WordTrace (prefixWord ++ tailWord_2095321) baseStart_2095321 baseEnd_2095321 := by
    simpa [prefixWord, tailWord_2095321, baseEnd_2095321] using wordTrace_append hprefix tailTrace_2095321
  have hstable : (prefixWord ++ tailWord_2095321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095321).length < 2 ^ (prefixWord ++ tailWord_2095321).sum := by decide
  have hdescent : baseEnd_2095321 < baseStart_2095321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095330 : List Nat := [3, 3, 4, 1, 1, 1, 2, 2, 4]
def baseStart_2095330 : Nat := 118140960795 + 2095330 * 2 ^ 59
def prefixEnd_2095330 : Nat := 4983230072969 + 3 ^ 40 * 2095330 * 2
def baseEnd_2095330 : Nat := 478182853237952109083893

theorem tailTrace_2095330 : CollatzResearch.WordTrace tailWord_2095330 prefixEnd_2095330 478182853237952109083893 := by
  unfold tailWord_2095330
  simp only [CollatzResearch.WordTrace]
  refine ⟨19105740874746184679726861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50948642332656492479271629 19105740874746184679726861)
  ·
    refine ⟨7164652828029819254897573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19105740874746184679726861 7164652828029819254897573)
    ·
      refine ⟨1343372405255591110293295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7164652828029819254897573 1343372405255591110293295)
      ·
        refine ⟨2015058607883386665439943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1343372405255591110293295 2015058607883386665439943)
        ·
          refine ⟨3022587911825079998159915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2015058607883386665439943 3022587911825079998159915)
          ·
            refine ⟨4533881867737619997239873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3022587911825079998159915 4533881867737619997239873)
            ·
              refine ⟨3400411400803214997929905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4533881867737619997239873 3400411400803214997929905)
              ·
                refine ⟨2550308550602411248447429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3400411400803214997929905 2550308550602411248447429)
                ·
                  refine ⟨478182853237952109083893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2550308550602411248447429 478182853237952109083893)
                  ·
                    rfl

theorem cell21_2095330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_2095330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2095330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2095330 prefixEnd_2095330 := by exact prefixLift 2095330
  have htrace : WordTrace (prefixWord ++ tailWord_2095330) baseStart_2095330 baseEnd_2095330 := by
    simpa [prefixWord, tailWord_2095330, baseEnd_2095330] using wordTrace_append hprefix tailTrace_2095330
  have hstable : (prefixWord ++ tailWord_2095330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095330).length < 2 ^ (prefixWord ++ tailWord_2095330).sum := by decide
  have hdescent : baseEnd_2095330 < baseStart_2095330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095369 : List Nat := [1, 2, 1, 1, 3, 5, 3, 5]
def baseStart_2095369 : Nat := 118140960795 + 2095369 * 2 ^ 59
def prefixEnd_2095369 : Nat := 4983230072969 + 3 ^ 40 * 2095369 * 2
def baseEnd_2095369 : Nat := 159397251189765569311271

theorem tailTrace_2095369 : CollatzResearch.WordTrace tailWord_2095369 prefixEnd_2095369 159397251189765569311271 := by
  unfold tailWord_2095369
  simp only [CollatzResearch.WordTrace]
  refine ⟨76424385945843448379577161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50949590630562298919718107 76424385945843448379577161)
  ·
    refine ⟨57318289459382586284682871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76424385945843448379577161 57318289459382586284682871)
    ·
      refine ⟨85977434189073879427024307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57318289459382586284682871 85977434189073879427024307)
      ·
        refine ⟨128966151283610819140536461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85977434189073879427024307 128966151283610819140536461)
        ·
          refine ⟨48362306731354057177701173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128966151283610819140536461 48362306731354057177701173)
          ·
            refine ⟨4533966256064442860409485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48362306731354057177701173 4533966256064442860409485)
            ·
              refine ⟨1700237346024166072653557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4533966256064442860409485 1700237346024166072653557)
              ·
                refine ⟨159397251189765569311271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1700237346024166072653557 159397251189765569311271)
                ·
                  rfl

theorem cell21_2095369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 5].length) (baseStart_2095369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2095369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2095369 prefixEnd_2095369 := by exact prefixLift 2095369
  have htrace : WordTrace (prefixWord ++ tailWord_2095369) baseStart_2095369 baseEnd_2095369 := by
    simpa [prefixWord, tailWord_2095369, baseEnd_2095369] using wordTrace_append hprefix tailTrace_2095369
  have hstable : (prefixWord ++ tailWord_2095369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095369).length < 2 ^ (prefixWord ++ tailWord_2095369).sum := by decide
  have hdescent : baseEnd_2095369 < baseStart_2095369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095389 : List Nat := [1, 4, 2, 3, 3, 1, 1, 2, 4]
def baseStart_2095389 : Nat := 118140960795 + 2095389 * 2 ^ 59
def prefixEnd_2095389 : Nat := 4983230072969 + 3 ^ 40 * 2095389 * 2
def baseEnd_2095389 : Nat := 478196317841781117600439

theorem tailTrace_2095389 : CollatzResearch.WordTrace tailWord_2095389 prefixEnd_2095389 478196317841781117600439 := by
  unfold tailWord_2095389
  simp only [CollatzResearch.WordTrace]
  refine ⟨76425115405770991795305221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50950076937180661196870147 76425115405770991795305221)
  ·
    refine ⟨14329709138582060961619729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76425115405770991795305221 14329709138582060961619729)
    ·
      refine ⟨10747281853936545721214797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14329709138582060961619729 10747281853936545721214797)
      ·
        refine ⟨4030230695226204645455549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10747281853936545721214797 4030230695226204645455549)
        ·
          refine ⟨1511336510709826742045831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4030230695226204645455549 1511336510709826742045831)
          ·
            refine ⟨2267004766064740113068747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1511336510709826742045831 2267004766064740113068747)
            ·
              refine ⟨3400507149097110169603121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2267004766064740113068747 3400507149097110169603121)
              ·
                refine ⟨2550380361822832627202341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3400507149097110169603121 2550380361822832627202341)
                ·
                  refine ⟨478196317841781117600439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2550380361822832627202341 478196317841781117600439)
                  ·
                    rfl

theorem cell21_2095389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 2, 4].length) (baseStart_2095389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2095389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2095389 prefixEnd_2095389 := by exact prefixLift 2095389
  have htrace : WordTrace (prefixWord ++ tailWord_2095389) baseStart_2095389 baseEnd_2095389 := by
    simpa [prefixWord, tailWord_2095389, baseEnd_2095389] using wordTrace_append hprefix tailTrace_2095389
  have hstable : (prefixWord ++ tailWord_2095389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095389).length < 2 ^ (prefixWord ++ tailWord_2095389).sum := by decide
  have hdescent : baseEnd_2095389 < baseStart_2095389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095445 : List Nat := [1, 3, 2, 2, 4, 2, 7]
def baseStart_2095445 : Nat := 118140960795 + 2095445 * 2 ^ 59
def prefixEnd_2095445 : Nat := 4983230072969 + 3 ^ 40 * 2095445 * 2
def baseEnd_2095445 : Nat := 53134344200526384962999

theorem tailTrace_2095445 : CollatzResearch.WordTrace tailWord_2095445 prefixEnd_2095445 53134344200526384962999 := by
  unfold tailWord_2095445
  simp only [CollatzResearch.WordTrace]
  refine ⟨76427157893568113359343789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50951438595712075572895859 76427157893568113359343789)
  ·
    refine ⟨28660184210088042509753921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76427157893568113359343789 28660184210088042509753921)
    ·
      refine ⟨21495138157566031882315441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28660184210088042509753921 21495138157566031882315441)
      ·
        refine ⟨16121353618174523911736581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21495138157566031882315441 16121353618174523911736581)
        ·
          refine ⟨3022753803407723233450609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16121353618174523911736581 3022753803407723233450609)
          ·
            refine ⟨2267065352555792425087957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3022753803407723233450609 2267065352555792425087957)
            ·
              refine ⟨53134344200526384962999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2267065352555792425087957 53134344200526384962999)
              ·
                rfl

theorem cell21_2095445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 7].length) (baseStart_2095445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2095445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2095445 prefixEnd_2095445 := by exact prefixLift 2095445
  have htrace : WordTrace (prefixWord ++ tailWord_2095445) baseStart_2095445 baseEnd_2095445 := by
    simpa [prefixWord, tailWord_2095445, baseEnd_2095445] using wordTrace_append hprefix tailTrace_2095445
  have hstable : (prefixWord ++ tailWord_2095445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095445).length < 2 ^ (prefixWord ++ tailWord_2095445).sum := by decide
  have hdescent : baseEnd_2095445 < baseStart_2095445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095583 : List Nat := [1, 1, 2, 3, 3, 3, 3, 1, 4]
def baseStart_2095583 : Nat := 118140960795 + 2095583 * 2 ^ 59
def prefixEnd_2095583 : Nat := 4983230072969 + 3 ^ 40 * 2095583 * 2
def baseEnd_2095583 : Nat := 478240591284879891366709

theorem tailTrace_2095583 : CollatzResearch.WordTrace tailWord_2095583 prefixEnd_2095583 478240591284879891366709 := by
  unfold tailWord_2095583
  simp only [CollatzResearch.WordTrace]
  refine ⟨76432191167068162927867403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50954794111378775285244935 76432191167068162927867403)
  ·
    refine ⟨114648286750602244391801105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76432191167068162927867403 114648286750602244391801105)
    ·
      refine ⟨85986215062951683293850829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114648286750602244391801105 85986215062951683293850829)
      ·
        refine ⟨32244830648606881235194061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85986215062951683293850829 32244830648606881235194061)
        ·
          refine ⟨12091811493227580463197773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32244830648606881235194061 12091811493227580463197773)
          ·
            refine ⟨4534429309960342673699165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12091811493227580463197773 4534429309960342673699165)
            ·
              refine ⟨1700410991235128502637187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4534429309960342673699165 1700410991235128502637187)
              ·
                refine ⟨2550616486852692753955781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1700410991235128502637187 2550616486852692753955781)
                ·
                  refine ⟨478240591284879891366709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2550616486852692753955781 478240591284879891366709)
                  ·
                    rfl

theorem cell21_2095583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 1, 4].length) (baseStart_2095583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2095583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2095583 prefixEnd_2095583 := by exact prefixLift 2095583
  have htrace : WordTrace (prefixWord ++ tailWord_2095583) baseStart_2095583 baseEnd_2095583 := by
    simpa [prefixWord, tailWord_2095583, baseEnd_2095583] using wordTrace_append hprefix tailTrace_2095583
  have hstable : (prefixWord ++ tailWord_2095583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095583).length < 2 ^ (prefixWord ++ tailWord_2095583).sum := by decide
  have hdescent : baseEnd_2095583 < baseStart_2095583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095597 : List Nat := [1, 5, 1, 3, 1, 2, 1, 7]
def baseStart_2095597 : Nat := 118140960795 + 2095597 * 2 ^ 59
def prefixEnd_2095597 : Nat := 4983230072969 + 3 ^ 40 * 2095597 * 2
def baseEnd_2095597 : Nat := 159414595425206326044449

theorem tailTrace_2095597 : CollatzResearch.WordTrace tailWord_2095597 prefixEnd_2095597 159414595425206326044449 := by
  unfold tailWord_2095597
  simp only [CollatzResearch.WordTrace]
  refine ⟨76432701789017443318877045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50955134526011628879251363 76432701789017443318877045)
  ·
    refine ⟨7165565792720385311144723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76432701789017443318877045 7165565792720385311144723)
    ·
      refine ⟨10748348689080577966717085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7165565792720385311144723 10748348689080577966717085)
      ·
        refine ⟨4030630758405216737518907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10748348689080577966717085 4030630758405216737518907)
        ·
          refine ⟨6045946137607825106278361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4030630758405216737518907 6045946137607825106278361)
          ·
            refine ⟨4534459603205868829708771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6045946137607825106278361 4534459603205868829708771)
            ·
              refine ⟨6801689404808803244563157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4534459603205868829708771 6801689404808803244563157)
              ·
                refine ⟨159414595425206326044449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6801689404808803244563157 159414595425206326044449)
                ·
                  rfl

theorem cell21_2095597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 7].length) (baseStart_2095597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2095597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2095597 prefixEnd_2095597 := by exact prefixLift 2095597
  have htrace : WordTrace (prefixWord ++ tailWord_2095597) baseStart_2095597 baseEnd_2095597 := by
    simpa [prefixWord, tailWord_2095597, baseEnd_2095597] using wordTrace_append hprefix tailTrace_2095597
  have hstable : (prefixWord ++ tailWord_2095597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095597).length < 2 ^ (prefixWord ++ tailWord_2095597).sum := by decide
  have hdescent : baseEnd_2095597 < baseStart_2095597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095628 : List Nat := [2, 2, 1, 2, 4, 3, 1, 1, 5]
def baseStart_2095628 : Nat := 118140960795 + 2095628 * 2 ^ 59
def prefixEnd_2095628 : Nat := 4983230072969 + 3 ^ 40 * 2095628 * 2
def baseEnd_2095628 : Nat := 478250860897969813116617

theorem tailTrace_2095628 : CollatzResearch.WordTrace tailWord_2095628 prefixEnd_2095628 478250860897969813116617 := by
  unfold tailWord_2095628
  simp only [CollatzResearch.WordTrace]
  refine ⟨38216916225952567806627769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50955888301270090408837025 38216916225952567806627769)
  ·
    refine ⟨28662687169464425854970827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38216916225952567806627769 28662687169464425854970827)
    ·
      refine ⟨42994030754196638782456241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28662687169464425854970827 42994030754196638782456241)
      ·
        refine ⟨32245523065647479086842181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42994030754196638782456241 32245523065647479086842181)
        ·
          refine ⟨6046035574808902328782909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32245523065647479086842181 6046035574808902328782909)
          ·
            refine ⟨2267263340553338373293591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6046035574808902328782909 2267263340553338373293591)
            ·
              refine ⟨3400895010830007559940387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2267263340553338373293591 3400895010830007559940387)
              ·
                refine ⟨5101342516245011339910581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3400895010830007559940387 5101342516245011339910581)
                ·
                  refine ⟨478250860897969813116617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5101342516245011339910581 478250860897969813116617)
                  ·
                    rfl

theorem cell21_2095628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 5].length) (baseStart_2095628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2095628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2095628 prefixEnd_2095628 := by exact prefixLift 2095628
  have htrace : WordTrace (prefixWord ++ tailWord_2095628) baseStart_2095628 baseEnd_2095628 := by
    simpa [prefixWord, tailWord_2095628, baseEnd_2095628] using wordTrace_append hprefix tailTrace_2095628
  have hstable : (prefixWord ++ tailWord_2095628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095628).length < 2 ^ (prefixWord ++ tailWord_2095628).sum := by decide
  have hdescent : baseEnd_2095628 < baseStart_2095628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095791 : List Nat := [1, 1, 2, 1, 2, 5, 9]
def baseStart_2095791 : Nat := 118140960795 + 2095791 * 2 ^ 59
def prefixEnd_2095791 : Nat := 4983230072969 + 3 ^ 40 * 2095791 * 2
def baseEnd_2095791 : Nat := 53143117746524194655513

theorem tailTrace_2095791 : CollatzResearch.WordTrace tailWord_2095791 prefixEnd_2095791 53143117746524194655513 := by
  unfold tailWord_2095791
  simp only [CollatzResearch.WordTrace]
  refine ⟨76439777550314614451439227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50959851700209742967626151 76439777550314614451439227)
  ·
    refine ⟨114659666325471921677158841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76439777550314614451439227 114659666325471921677158841)
    ·
      refine ⟨85994749744103941257869131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114659666325471921677158841 85994749744103941257869131)
      ·
        refine ⟨128992124616155911886803697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85994749744103941257869131 128992124616155911886803697)
        ·
          refine ⟨96744093462116933915102773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128992124616155911886803697 96744093462116933915102773)
          ·
            refine ⟨9069758762073462554540885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96744093462116933915102773 9069758762073462554540885)
            ·
              refine ⟨53143117746524194655513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 9069758762073462554540885 53143117746524194655513)
              ·
                rfl

theorem cell21_2095791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 9].length) (baseStart_2095791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2095791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2095791 prefixEnd_2095791 := by exact prefixLift 2095791
  have htrace : WordTrace (prefixWord ++ tailWord_2095791) baseStart_2095791 baseEnd_2095791 := by
    simpa [prefixWord, tailWord_2095791, baseEnd_2095791] using wordTrace_append hprefix tailTrace_2095791
  have hstable : (prefixWord ++ tailWord_2095791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095791).length < 2 ^ (prefixWord ++ tailWord_2095791).sum := by decide
  have hdescent : baseEnd_2095791 < baseStart_2095791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095808 : List Nat := [2, 1, 1, 2, 4, 3, 2, 6]
def baseStart_2095808 : Nat := 118140960795 + 2095808 * 2 ^ 59
def prefixEnd_2095808 : Nat := 4983230072969 + 3 ^ 40 * 2095808 * 2
def baseEnd_2095808 : Nat := 159430646450109833372083

theorem tailTrace_2095808 : CollatzResearch.WordTrace tailWord_2095808 prefixEnd_2095808 159430646450109833372083 := by
  unfold tailWord_2095808
  simp only [CollatzResearch.WordTrace]
  refine ⟨38220198795626513177404039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50960265060835350903205385 38220198795626513177404039)
  ·
    refine ⟨57330298193439769766106059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38220198795626513177404039 57330298193439769766106059)
    ·
      refine ⟨85995447290159654649159089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57330298193439769766106059 85995447290159654649159089)
      ·
        refine ⟨64496585467619740986869317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85995447290159654649159089 64496585467619740986869317)
        ·
          refine ⟨12093109775178701435037997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64496585467619740986869317 12093109775178701435037997)
          ·
            refine ⟨4534916165692013038139249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12093109775178701435037997 4534916165692013038139249)
            ·
              refine ⟨3401187124269009778604437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4534916165692013038139249 3401187124269009778604437)
              ·
                refine ⟨159430646450109833372083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3401187124269009778604437 159430646450109833372083)
                ·
                  rfl

theorem cell21_2095808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 6].length) (baseStart_2095808 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2095808 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2095808 prefixEnd_2095808 := by exact prefixLift 2095808
  have htrace : WordTrace (prefixWord ++ tailWord_2095808) baseStart_2095808 baseEnd_2095808 := by
    simpa [prefixWord, tailWord_2095808, baseEnd_2095808] using wordTrace_append hprefix tailTrace_2095808
  have hstable : (prefixWord ++ tailWord_2095808).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095808).length < 2 ^ (prefixWord ++ tailWord_2095808).sum := by decide
  have hdescent : baseEnd_2095808 < baseStart_2095808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095890 : List Nat := [3, 2, 4, 1, 2, 1, 2, 3, 3]
def baseStart_2095890 : Nat := 118140960795 + 2095890 * 2 ^ 59
def prefixEnd_2095890 : Nat := 4983230072969 + 3 ^ 40 * 2095890 * 2
def baseEnd_2095890 : Nat := 478310652867515579749415

theorem tailTrace_2095890 : CollatzResearch.WordTrace tailWord_2095890 prefixEnd_2095890 478310652867515579749415 := by
  unfold tailWord_2095890
  simp only [CollatzResearch.WordTrace]
  refine ⟨19110847094238988589823281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50962258917970636239528749 19110847094238988589823281)
  ·
    refine ⟨14333135320679241442367461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19110847094238988589823281 14333135320679241442367461)
    ·
      refine ⟨2687462872627357770443899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14333135320679241442367461 2687462872627357770443899)
      ·
        refine ⟨4031194308941036655665849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2687462872627357770443899 4031194308941036655665849)
        ·
          refine ⟨3023395731705777491749387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4031194308941036655665849 3023395731705777491749387)
          ·
            refine ⟨4535093597558666237624081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3023395731705777491749387 4535093597558666237624081)
            ·
              refine ⟨3401320198168999678218061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4535093597558666237624081 3401320198168999678218061)
              ·
                refine ⟨1275495074313374879331773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3401320198168999678218061 1275495074313374879331773)
                ·
                  refine ⟨478310652867515579749415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1275495074313374879331773 478310652867515579749415)
                  ·
                    rfl

theorem cell21_2095890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 3, 3].length) (baseStart_2095890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2095890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2095890 prefixEnd_2095890 := by exact prefixLift 2095890
  have htrace : WordTrace (prefixWord ++ tailWord_2095890) baseStart_2095890 baseEnd_2095890 := by
    simpa [prefixWord, tailWord_2095890, baseEnd_2095890] using wordTrace_append hprefix tailTrace_2095890
  have hstable : (prefixWord ++ tailWord_2095890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095890).length < 2 ^ (prefixWord ++ tailWord_2095890).sum := by decide
  have hdescent : baseEnd_2095890 < baseStart_2095890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095898 : List Nat := [3, 1, 1, 3, 2, 1, 1, 2, 7]
def baseStart_2095898 : Nat := 118140960795 + 2095898 * 2 ^ 59
def prefixEnd_2095898 : Nat := 4983230072969 + 3 ^ 40 * 2095898 * 2
def baseEnd_2095898 : Nat := 478312478576509343616065

theorem tailTrace_2095898 : CollatzResearch.WordTrace tailWord_2095898 prefixEnd_2095898 478312478576509343616065 := by
  unfold tailWord_2095898
  simp only [CollatzResearch.WordTrace]
  refine ⟨19110920040231742931396087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50962453440617981150389565 19110920040231742931396087)
  ·
    refine ⟨28666380060347614397094131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19110920040231742931396087 28666380060347614397094131)
    ·
      refine ⟨42999570090521421595641197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28666380060347614397094131 42999570090521421595641197)
      ·
        refine ⟨16124838783945533098365449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42999570090521421595641197 16124838783945533098365449)
        ·
          refine ⟨12093629087959149823774087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16124838783945533098365449 12093629087959149823774087)
          ·
            refine ⟨18140443631938724735661131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12093629087959149823774087 18140443631938724735661131)
            ·
              refine ⟨27210665447908087103491697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18140443631938724735661131 27210665447908087103491697)
              ·
                refine ⟨20407999085931065327618773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27210665447908087103491697 20407999085931065327618773)
                ·
                  refine ⟨478312478576509343616065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20407999085931065327618773 478312478576509343616065)
                  ·
                    rfl

theorem cell21_2095898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_2095898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2095898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2095898 prefixEnd_2095898 := by exact prefixLift 2095898
  have htrace : WordTrace (prefixWord ++ tailWord_2095898) baseStart_2095898 baseEnd_2095898 := by
    simpa [prefixWord, tailWord_2095898, baseEnd_2095898] using wordTrace_append hprefix tailTrace_2095898
  have hstable : (prefixWord ++ tailWord_2095898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095898).length < 2 ^ (prefixWord ++ tailWord_2095898).sum := by decide
  have hdescent : baseEnd_2095898 < baseStart_2095898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095901 : List Nat := [1, 4, 2, 4, 1, 1, 8]
def baseStart_2095901 : Nat := 118140960795 + 2095901 * 2 ^ 59
def prefixEnd_2095901 : Nat := 4983230072969 + 3 ^ 40 * 2095901 * 2
def baseEnd_2095901 : Nat := 53145907024153556118451

theorem tailTrace_2095901 : CollatzResearch.WordTrace tailWord_2095901 prefixEnd_2095901 53145907024153556118451 := by
  unfold tailWord_2095901
  simp only [CollatzResearch.WordTrace]
  refine ⟨76443789579916103237943557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50962526386610735491962371 76443789579916103237943557)
  ·
    refine ⟨14333210546234269357114417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76443789579916103237943557 14333210546234269357114417)
    ·
      refine ⟨10749907909675702017835813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14333210546234269357114417 10749907909675702017835813)
      ·
        refine ⟨2015607733064194128344215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10749907909675702017835813 2015607733064194128344215)
        ·
          refine ⟨3023411599596291192516323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2015607733064194128344215 3023411599596291192516323)
          ·
            refine ⟨4535117399394436788774485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3023411599596291192516323 4535117399394436788774485)
            ·
              refine ⟨53145907024153556118451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4535117399394436788774485 53145907024153556118451)
              ·
                rfl

theorem cell21_2095901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 8].length) (baseStart_2095901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2095901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2095901 prefixEnd_2095901 := by exact prefixLift 2095901
  have htrace : WordTrace (prefixWord ++ tailWord_2095901) baseStart_2095901 baseEnd_2095901 := by
    simpa [prefixWord, tailWord_2095901, baseEnd_2095901] using wordTrace_append hprefix tailTrace_2095901
  have hstable : (prefixWord ++ tailWord_2095901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095901).length < 2 ^ (prefixWord ++ tailWord_2095901).sum := by decide
  have hdescent : baseEnd_2095901 < baseStart_2095901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096084 : List Nat := [2, 4, 1, 2, 1, 2, 2, 4, 3]
def baseStart_2096084 : Nat := 118140960795 + 2096084 * 2 ^ 59
def prefixEnd_2096084 : Nat := 4983230072969 + 3 ^ 40 * 2096084 * 2
def baseEnd_2096084 : Nat := 478354926310614353515685

theorem tailTrace_2096084 : CollatzResearch.WordTrace tailWord_2096084 prefixEnd_2096084 478354926310614353515685 := by
  unfold tailWord_2096084
  simp only [CollatzResearch.WordTrace]
  refine ⟨38225232069126562745927653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50966976092168750327903537 38225232069126562745927653)
  ·
    refine ⟨7167231012961230514861435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38225232069126562745927653 7167231012961230514861435)
    ·
      refine ⟨10750846519441845772292153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7167231012961230514861435 10750846519441845772292153)
      ·
        refine ⟨8063134889581384329219115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10750846519441845772292153 8063134889581384329219115)
        ·
          refine ⟨12094702334372076493828673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8063134889581384329219115 12094702334372076493828673)
          ·
            refine ⟨9071026750779057370371505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12094702334372076493828673 9071026750779057370371505)
            ·
              refine ⟨6803270063084293027778629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9071026750779057370371505 6803270063084293027778629)
              ·
                refine ⟨1275613136828304942708493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6803270063084293027778629 1275613136828304942708493)
                ·
                  refine ⟨478354926310614353515685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1275613136828304942708493 478354926310614353515685)
                  ·
                    rfl

theorem cell21_2096084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_2096084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2096084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2096084 prefixEnd_2096084 := by exact prefixLift 2096084
  have htrace : WordTrace (prefixWord ++ tailWord_2096084) baseStart_2096084 baseEnd_2096084 := by
    simpa [prefixWord, tailWord_2096084, baseEnd_2096084] using wordTrace_append hprefix tailTrace_2096084
  have hstable : (prefixWord ++ tailWord_2096084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096084).length < 2 ^ (prefixWord ++ tailWord_2096084).sum := by decide
  have hdescent : baseEnd_2096084 < baseStart_2096084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096205 : List Nat := [1, 6, 1, 1, 1, 4, 1, 6]
def baseStart_2096205 : Nat := 118140960795 + 2096205 * 2 ^ 59
def prefixEnd_2096205 : Nat := 4983230072969 + 3 ^ 40 * 2096205 * 2
def baseEnd_2096205 : Nat := 159460846719715010666257

theorem tailTrace_2096205 : CollatzResearch.WordTrace tailWord_2096205 prefixEnd_2096205 159460846719715010666257 := by
  unfold tailWord_2096205
  simp only [CollatzResearch.WordTrace]
  refine ⟨76454877370814763157010069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50969918247209842104673379 76454877370814763157010069)
  ·
    refine ⟨3583822376756942022984847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 76454877370814763157010069 3583822376756942022984847)
    ·
      refine ⟨5375733565135413034477271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3583822376756942022984847 5375733565135413034477271)
      ·
        refine ⟨8063600347703119551715907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5375733565135413034477271 8063600347703119551715907)
        ·
          refine ⟨12095400521554679327573861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8063600347703119551715907 12095400521554679327573861)
          ·
            refine ⟨2267887597791502373920099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12095400521554679327573861 2267887597791502373920099)
            ·
              refine ⟨3401831396687253560880149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2267887597791502373920099 3401831396687253560880149)
              ·
                refine ⟨159460846719715010666257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3401831396687253560880149 159460846719715010666257)
                ·
                  rfl

theorem cell21_2096205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 6].length) (baseStart_2096205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2096205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2096205 prefixEnd_2096205 := by exact prefixLift 2096205
  have htrace : WordTrace (prefixWord ++ tailWord_2096205) baseStart_2096205 baseEnd_2096205 := by
    simpa [prefixWord, tailWord_2096205, baseEnd_2096205] using wordTrace_append hprefix tailTrace_2096205
  have hstable : (prefixWord ++ tailWord_2096205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096205).length < 2 ^ (prefixWord ++ tailWord_2096205).sum := by decide
  have hdescent : baseEnd_2096205 < baseStart_2096205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096337 : List Nat := [1, 2, 2, 1, 2, 2, 1, 3, 7]
def baseStart_2096337 : Nat := 118140960795 + 2096337 * 2 ^ 59
def prefixEnd_2096337 : Nat := 4983230072969 + 3 ^ 40 * 2096337 * 2
def baseEnd_2096337 : Nat := 478412664357542135798501

theorem tailTrace_2096337 : CollatzResearch.WordTrace tailWord_2096337 prefixEnd_2096337 478412664357542135798501 := by
  unfold tailWord_2096337
  simp only [CollatzResearch.WordTrace]
  refine ⟨76459691806336549700815265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50973127870891033133876843 76459691806336549700815265)
  ·
    refine ⟨57344768854752412275611449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76459691806336549700815265 57344768854752412275611449)
    ·
      refine ⟨43008576641064309206708587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57344768854752412275611449 43008576641064309206708587)
      ·
        refine ⟨64512864961596463810062881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43008576641064309206708587 64512864961596463810062881)
        ·
          refine ⟨48384648721197347857547161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64512864961596463810062881 48384648721197347857547161)
          ·
            refine ⟨36288486540898010893160371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48384648721197347857547161 36288486540898010893160371)
            ·
              refine ⟨54432729811347016339740557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36288486540898010893160371 54432729811347016339740557)
              ·
                refine ⟨20412273679255131127402709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54432729811347016339740557 20412273679255131127402709)
                ·
                  refine ⟨478412664357542135798501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20412273679255131127402709 478412664357542135798501)
                  ·
                    rfl

theorem cell21_2096337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 7].length) (baseStart_2096337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2096337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2096337 prefixEnd_2096337 := by exact prefixLift 2096337
  have htrace : WordTrace (prefixWord ++ tailWord_2096337) baseStart_2096337 baseEnd_2096337 := by
    simpa [prefixWord, tailWord_2096337, baseEnd_2096337] using wordTrace_append hprefix tailTrace_2096337
  have hstable : (prefixWord ++ tailWord_2096337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096337).length < 2 ^ (prefixWord ++ tailWord_2096337).sum := by decide
  have hdescent : baseEnd_2096337 < baseStart_2096337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096371 : List Nat := [1, 1, 1, 2, 2, 6, 1, 4, 3]
def baseStart_2096371 : Nat := 118140960795 + 2096371 * 2 ^ 59
def prefixEnd_2096371 : Nat := 4983230072969 + 3 ^ 40 * 2096371 * 2
def baseEnd_2096371 : Nat := 478420423620765632231765

theorem tailTrace_2096371 : CollatzResearch.WordTrace tailWord_2096371 prefixEnd_2096371 478420423620765632231765 := by
  unfold tailWord_2096371
  simp only [CollatzResearch.WordTrace]
  refine ⟨76460931888213373507552967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50973954592142249005035311 76460931888213373507552967)
  ·
    refine ⟨114691397832320060261329451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76460931888213373507552967 114691397832320060261329451)
    ·
      refine ⟨172037096748480090391994177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114691397832320060261329451 172037096748480090391994177)
      ·
        refine ⟨129027822561360067793995633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172037096748480090391994177 129027822561360067793995633)
        ·
          refine ⟨96770866921020050845496725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129027822561360067793995633 96770866921020050845496725)
          ·
            refine ⟨4536134386922814883382659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 96770866921020050845496725 4536134386922814883382659)
            ·
              refine ⟨6804201580384222325073989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4536134386922814883382659 6804201580384222325073989)
              ·
                refine ⟨1275787796322041685951373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6804201580384222325073989 1275787796322041685951373)
                ·
                  refine ⟨478420423620765632231765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1275787796322041685951373 478420423620765632231765)
                  ·
                    rfl

theorem cell21_2096371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 4, 3].length) (baseStart_2096371 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2096371 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2096371 prefixEnd_2096371 := by exact prefixLift 2096371
  have htrace : WordTrace (prefixWord ++ tailWord_2096371) baseStart_2096371 baseEnd_2096371 := by
    simpa [prefixWord, tailWord_2096371, baseEnd_2096371] using wordTrace_append hprefix tailTrace_2096371
  have hstable : (prefixWord ++ tailWord_2096371).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096371).length < 2 ^ (prefixWord ++ tailWord_2096371).sum := by decide
  have hdescent : baseEnd_2096371 < baseStart_2096371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096385 : List Nat := [1, 2, 4, 1, 1, 3, 2, 3, 4]
def baseStart_2096385 : Nat := 118140960795 + 2096385 * 2 ^ 59
def prefixEnd_2096385 : Nat := 4983230072969 + 3 ^ 40 * 2096385 * 2
def baseEnd_2096385 : Nat := 478423618611504718998403

theorem tailTrace_2096385 : CollatzResearch.WordTrace tailWord_2096385 prefixEnd_2096385 478423618611504718998403 := by
  unfold tailWord_2096385
  simp only [CollatzResearch.WordTrace]
  refine ⟨76461442510162653898562609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50974295006775102599041739 76461442510162653898562609)
  ·
    refine ⟨57346081882621990423921957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76461442510162653898562609 57346081882621990423921957)
    ·
      refine ⟨10752390352991623204485367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57346081882621990423921957 10752390352991623204485367)
      ·
        refine ⟨16128585529487434806728051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10752390352991623204485367 16128585529487434806728051)
        ·
          refine ⟨24192878294231152210092077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16128585529487434806728051 24192878294231152210092077)
          ·
            refine ⟨9072329360336682078784529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24192878294231152210092077 9072329360336682078784529)
            ·
              refine ⟨6804247020252511559088397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9072329360336682078784529 6804247020252511559088397)
              ·
                refine ⟨2551592632594691834658149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6804247020252511559088397 2551592632594691834658149)
                ·
                  refine ⟨478423618611504718998403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2551592632594691834658149 478423618611504718998403)
                  ·
                    rfl

theorem cell21_2096385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 3, 4].length) (baseStart_2096385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2096385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2096385 prefixEnd_2096385 := by exact prefixLift 2096385
  have htrace : WordTrace (prefixWord ++ tailWord_2096385) baseStart_2096385 baseEnd_2096385 := by
    simpa [prefixWord, tailWord_2096385, baseEnd_2096385] using wordTrace_append hprefix tailTrace_2096385
  have hstable : (prefixWord ++ tailWord_2096385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096385).length < 2 ^ (prefixWord ++ tailWord_2096385).sum := by decide
  have hdescent : baseEnd_2096385 < baseStart_2096385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096489 : List Nat := [1, 2, 1, 1, 1, 3, 2, 5, 5]
def baseStart_2096489 : Nat := 118140960795 + 2096489 * 2 ^ 59
def prefixEnd_2096489 : Nat := 4983230072969 + 3 ^ 40 * 2096489 * 2
def baseEnd_2096489 : Nat := 478447352828423649264857

theorem tailTrace_2096489 : CollatzResearch.WordTrace tailWord_2096489 prefixEnd_2096489 478447352828423649264857 := by
  unfold tailWord_2096489
  simp only [CollatzResearch.WordTrace]
  refine ⟨76465235701785879660348521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50976823801190586440232347 76465235701785879660348521)
  ·
    refine ⟨57348926776339409745261391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76465235701785879660348521 57348926776339409745261391)
    ·
      refine ⟨86023390164509114617892087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57348926776339409745261391 86023390164509114617892087)
      ·
        refine ⟨129035085246763671926838131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86023390164509114617892087 129035085246763671926838131)
        ·
          refine ⟨193552627870145507890257197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129035085246763671926838131 193552627870145507890257197)
          ·
            refine ⟨72582235451304565458846449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193552627870145507890257197 72582235451304565458846449)
            ·
              refine ⟨54436676588478424094134837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72582235451304565458846449 54436676588478424094134837)
              ·
                refine ⟨5103438430169852258825141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54436676588478424094134837 5103438430169852258825141)
                ·
                  refine ⟨478447352828423649264857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5103438430169852258825141 478447352828423649264857)
                  ·
                    rfl

theorem cell21_2096489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 5].length) (baseStart_2096489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2096489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2096489 prefixEnd_2096489 := by exact prefixLift 2096489
  have htrace : WordTrace (prefixWord ++ tailWord_2096489) baseStart_2096489 baseEnd_2096489 := by
    simpa [prefixWord, tailWord_2096489, baseEnd_2096489] using wordTrace_append hprefix tailTrace_2096489
  have hstable : (prefixWord ++ tailWord_2096489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096489).length < 2 ^ (prefixWord ++ tailWord_2096489).sum := by decide
  have hdescent : baseEnd_2096489 < baseStart_2096489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096537 : List Nat := [1, 2, 1, 2, 1, 6, 2, 2, 4]
def baseStart_2096537 : Nat := 118140960795 + 2096537 * 2 ^ 59
def prefixEnd_2096537 : Nat := 4983230072969 + 3 ^ 40 * 2096537 * 2
def baseEnd_2096537 : Nat := 478458307082386232464759

theorem tailTrace_2096537 : CollatzResearch.WordTrace tailWord_2096537 prefixEnd_2096537 478458307082386232464759 := by
  unfold tailWord_2096537
  simp only [CollatzResearch.WordTrace]
  refine ⟨76466986405611983858095865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50977990937074655905397243 76466986405611983858095865)
  ·
    refine ⟨57350239804208987893571899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76466986405611983858095865 57350239804208987893571899)
    ·
      refine ⟨86025359706313481840357849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57350239804208987893571899 86025359706313481840357849)
      ·
        refine ⟨64519019779735111380268387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86025359706313481840357849 64519019779735111380268387)
        ·
          refine ⟨96778529669602667070402581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64519019779735111380268387 96778529669602667070402581)
          ·
            refine ⟨4536493578262625018925121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 96778529669602667070402581 4536493578262625018925121)
            ·
              refine ⟨3402370183696968764193841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4536493578262625018925121 3402370183696968764193841)
              ·
                refine ⟨2551777637772726573145381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3402370183696968764193841 2551777637772726573145381)
                ·
                  refine ⟨478458307082386232464759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2551777637772726573145381 478458307082386232464759)
                  ·
                    rfl

theorem cell21_2096537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 2, 4].length) (baseStart_2096537 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2096537 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2096537 prefixEnd_2096537 := by exact prefixLift 2096537
  have htrace : WordTrace (prefixWord ++ tailWord_2096537) baseStart_2096537 baseEnd_2096537 := by
    simpa [prefixWord, tailWord_2096537, baseEnd_2096537] using wordTrace_append hprefix tailTrace_2096537
  have hstable : (prefixWord ++ tailWord_2096537).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096537).length < 2 ^ (prefixWord ++ tailWord_2096537).sum := by decide
  have hdescent : baseEnd_2096537 < baseStart_2096537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096644 : List Nat := [2, 3, 2, 3, 2, 2, 7]
def baseStart_2096644 : Nat := 118140960795 + 2096644 * 2 ^ 59
def prefixEnd_2096644 : Nat := 4983230072969 + 3 ^ 40 * 2096644 * 2
def baseEnd_2096644 : Nat := 53164747326686424909023

theorem tailTrace_2096644 : CollatzResearch.WordTrace tailWord_2096644 prefixEnd_2096644 53164747326686424909023 := by
  unfold tailWord_2096644
  simp only [CollatzResearch.WordTrace]
  refine ⟨38235444508112170566120493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50980592677482894088160657 38235444508112170566120493)
  ·
    refine ⟨14338291690542063962295185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38235444508112170566120493 14338291690542063962295185)
    ·
      refine ⟨10753718767906547971721389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14338291690542063962295185 10753718767906547971721389)
      ·
        refine ⟨4032644537964955489395521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10753718767906547971721389 4032644537964955489395521)
        ·
          refine ⟨3024483403473716617046641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4032644537964955489395521 3024483403473716617046641)
          ·
            refine ⟨2268362552605287462784981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3024483403473716617046641 2268362552605287462784981)
            ·
              refine ⟨53164747326686424909023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2268362552605287462784981 53164747326686424909023)
              ·
                rfl

theorem cell21_2096644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 7].length) (baseStart_2096644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2096644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2096644 prefixEnd_2096644 := by exact prefixLift 2096644
  have htrace : WordTrace (prefixWord ++ tailWord_2096644) baseStart_2096644 baseEnd_2096644 := by
    simpa [prefixWord, tailWord_2096644, baseEnd_2096644] using wordTrace_append hprefix tailTrace_2096644
  have hstable : (prefixWord ++ tailWord_2096644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096644).length < 2 ^ (prefixWord ++ tailWord_2096644).sum := by decide
  have hdescent : baseEnd_2096644 < baseStart_2096644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096655 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 10]
def baseStart_2096655 : Nat := 118140960795 + 2096655 * 2 ^ 59
def prefixEnd_2096655 : Nat := 4983230072969 + 3 ^ 40 * 2096655 * 2
def baseEnd_2096655 : Nat := 478485236290044249497851

theorem tailTrace_2096655 : CollatzResearch.WordTrace tailWord_2096655 prefixEnd_2096655 478485236290044249497851 := by
  unfold tailWord_2096655
  simp only [CollatzResearch.WordTrace]
  refine ⟨76471290219184490010891419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50980860146122993340594279 76471290219184490010891419)
  ·
    refine ⟨114706935328776735016337129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76471290219184490010891419 114706935328776735016337129)
    ·
      refine ⟨86030201496582551262252847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114706935328776735016337129 86030201496582551262252847)
      ·
        refine ⟨129045302244873826893379271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86030201496582551262252847 129045302244873826893379271)
        ·
          refine ⟨193567953367310740340068907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129045302244873826893379271 193567953367310740340068907)
          ·
            refine ⟨290351930050966110510103361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193567953367310740340068907 290351930050966110510103361)
            ·
              refine ⟨217763947538224582882577521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290351930050966110510103361 217763947538224582882577521)
              ·
                refine ⟨163322960653668437161933141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217763947538224582882577521 163322960653668437161933141)
                ·
                  refine ⟨478485236290044249497851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 163322960653668437161933141 478485236290044249497851)
                  ·
                    rfl

theorem cell21_2096655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 10].length) (baseStart_2096655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2096655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2096655 prefixEnd_2096655 := by exact prefixLift 2096655
  have htrace : WordTrace (prefixWord ++ tailWord_2096655) baseStart_2096655 baseEnd_2096655 := by
    simpa [prefixWord, tailWord_2096655, baseEnd_2096655] using wordTrace_append hprefix tailTrace_2096655
  have hstable : (prefixWord ++ tailWord_2096655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096655).length < 2 ^ (prefixWord ++ tailWord_2096655).sum := by decide
  have hdescent : baseEnd_2096655 < baseStart_2096655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096765 : List Nat := [1, 4, 1, 1, 4, 1, 3, 2, 4]
def baseStart_2096765 : Nat := 118140960795 + 2096765 * 2 ^ 59
def prefixEnd_2096765 : Nat := 4983230072969 + 3 ^ 40 * 2096765 * 2
def baseEnd_2096765 : Nat := 478510339788708502664293

theorem tailTrace_2096765 : CollatzResearch.WordTrace tailWord_2096765 prefixEnd_2096765 478510339788708502664293 := by
  unfold tailWord_2096765
  simp only [CollatzResearch.WordTrace]
  refine ⟨76475302248785978797395749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50983534832523985864930499 76475302248785978797395749)
  ·
    refine ⟨14339119171647371024511703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76475302248785978797395749 14339119171647371024511703)
    ·
      refine ⟨21508678757471056536767555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14339119171647371024511703 21508678757471056536767555)
      ·
        refine ⟨32263018136206584805151333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21508678757471056536767555 32263018136206584805151333)
        ·
          refine ⟨6049315900538734650965875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32263018136206584805151333 6049315900538734650965875)
          ·
            refine ⟨9073973850808101976448813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6049315900538734650965875 9073973850808101976448813)
            ·
              refine ⟨3402740194053038241168305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9073973850808101976448813 3402740194053038241168305)
              ·
                refine ⟨2552055145539778680876229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3402740194053038241168305 2552055145539778680876229)
                ·
                  refine ⟨478510339788708502664293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2552055145539778680876229 478510339788708502664293)
                  ·
                    rfl

theorem cell21_2096765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_2096765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2096765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2096765 prefixEnd_2096765 := by exact prefixLift 2096765
  have htrace : WordTrace (prefixWord ++ tailWord_2096765) baseStart_2096765 baseEnd_2096765 := by
    simpa [prefixWord, tailWord_2096765, baseEnd_2096765] using wordTrace_append hprefix tailTrace_2096765
  have hstable : (prefixWord ++ tailWord_2096765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096765).length < 2 ^ (prefixWord ++ tailWord_2096765).sum := by decide
  have hdescent : baseEnd_2096765 < baseStart_2096765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096782 : List Nat := [4, 1, 1, 3, 1, 3, 3, 1, 4]
def baseStart_2096782 : Nat := 118140960795 + 2096782 * 2 ^ 59
def prefixEnd_2096782 : Nat := 4983230072969 + 3 ^ 40 * 2096782 * 2
def baseEnd_2096782 : Nat := 478514219420320250880925

theorem tailTrace_2096782 : CollatzResearch.WordTrace tailWord_2096782 prefixEnd_2096782 478514219420320250880925 := by
  unfold tailWord_2096782
  simp only [CollatzResearch.WordTrace]
  refine ⟨9559490286215548837595575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50983948193149593800509733 9559490286215548837595575)
  ·
    refine ⟨14339235429323323256393363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9559490286215548837595575 14339235429323323256393363)
    ·
      refine ⟨21508853143984984884590045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14339235429323323256393363 21508853143984984884590045)
      ·
        refine ⟨8065819928994369331721267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21508853143984984884590045 8065819928994369331721267)
        ·
          refine ⟨12098729893491553997581901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8065819928994369331721267 12098729893491553997581901)
          ·
            refine ⟨4537023710059332749093213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12098729893491553997581901 4537023710059332749093213)
            ·
              refine ⟨1701383891272249780909955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4537023710059332749093213 1701383891272249780909955)
              ·
                refine ⟨2552075836908374671364933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1701383891272249780909955 2552075836908374671364933)
                ·
                  refine ⟨478514219420320250880925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2552075836908374671364933 478514219420320250880925)
                  ·
                    rfl

theorem cell21_2096782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_2096782 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2096782 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2096782 prefixEnd_2096782 := by exact prefixLift 2096782
  have htrace : WordTrace (prefixWord ++ tailWord_2096782) baseStart_2096782 baseEnd_2096782 := by
    simpa [prefixWord, tailWord_2096782, baseEnd_2096782] using wordTrace_append hprefix tailTrace_2096782
  have hstable : (prefixWord ++ tailWord_2096782).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096782).length < 2 ^ (prefixWord ++ tailWord_2096782).sum := by decide
  have hdescent : baseEnd_2096782 < baseStart_2096782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096802 : List Nat := [3, 3, 1, 4, 2, 1, 1, 3, 3]
def baseStart_2096802 : Nat := 118140960795 + 2096802 * 2 ^ 59
def prefixEnd_2096802 : Nat := 4983230072969 + 3 ^ 40 * 2096802 * 2
def baseEnd_2096802 : Nat := 478518783692804660547551

theorem tailTrace_2096802 : CollatzResearch.WordTrace tailWord_2096802 prefixEnd_2096802 478518783692804660547551 := by
  unfold tailWord_2096802
  simp only [CollatzResearch.WordTrace]
  refine ⟨19119162937412983529123165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50984434499767956077661773 19119162937412983529123165)
  ·
    refine ⟨7169686101529868823421187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19119162937412983529123165 7169686101529868823421187)
    ·
      refine ⟨10754529152294803235131781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7169686101529868823421187 10754529152294803235131781)
      ·
        refine ⟨2016474216055275606587209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10754529152294803235131781 2016474216055275606587209)
        ·
          refine ⟨1512355662041456704940407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2016474216055275606587209 1512355662041456704940407)
          ·
            refine ⟨2268533493062185057410611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1512355662041456704940407 2268533493062185057410611)
            ·
              refine ⟨3402800239593277586115917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2268533493062185057410611 3402800239593277586115917)
              ·
                refine ⟨1276050089847479094793469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3402800239593277586115917 1276050089847479094793469)
                ·
                  refine ⟨478518783692804660547551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1276050089847479094793469 478518783692804660547551)
                  ·
                    rfl

theorem cell21_2096802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_2096802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2096802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2096802 prefixEnd_2096802 := by exact prefixLift 2096802
  have htrace : WordTrace (prefixWord ++ tailWord_2096802) baseStart_2096802 baseEnd_2096802 := by
    simpa [prefixWord, tailWord_2096802, baseEnd_2096802] using wordTrace_append hprefix tailTrace_2096802
  have hstable : (prefixWord ++ tailWord_2096802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096802).length < 2 ^ (prefixWord ++ tailWord_2096802).sum := by decide
  have hdescent : baseEnd_2096802 < baseStart_2096802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096883 : List Nat := [1, 1, 1, 2, 2, 3, 2, 3, 6]
def baseStart_2096883 : Nat := 118140960795 + 2096883 * 2 ^ 59
def prefixEnd_2096883 : Nat := 4983230072969 + 3 ^ 40 * 2096883 * 2
def baseEnd_2096883 : Nat := 478537268996366519697385

theorem tailTrace_2096883 : CollatzResearch.WordTrace tailWord_2096883 prefixEnd_2096883 478537268996366519697385 := by
  unfold tailWord_2096883
  simp only [CollatzResearch.WordTrace]
  refine ⟨76479606062358484950191303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50986404041572323300127535 76479606062358484950191303)
  ·
    refine ⟨114719409093537727425286955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76479606062358484950191303 114719409093537727425286955)
    ·
      refine ⟨172079113640306591137930433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114719409093537727425286955 172079113640306591137930433)
      ·
        refine ⟨129059335230229943353447825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172079113640306591137930433 129059335230229943353447825)
        ·
          refine ⟨96794501422672457515085869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129059335230229943353447825 96794501422672457515085869)
          ·
            refine ⟨36297938033502171568157201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96794501422672457515085869 36297938033502171568157201)
            ·
              refine ⟨27223453525126628676117901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36297938033502171568157201 27223453525126628676117901)
              ·
                refine ⟨10208795071922485753544213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27223453525126628676117901 10208795071922485753544213)
                ·
                  refine ⟨478537268996366519697385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10208795071922485753544213 478537268996366519697385)
                  ·
                    rfl

theorem cell21_2096883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 6].length) (baseStart_2096883 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2096883 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2096883 prefixEnd_2096883 := by exact prefixLift 2096883
  have htrace : WordTrace (prefixWord ++ tailWord_2096883) baseStart_2096883 baseEnd_2096883 := by
    simpa [prefixWord, tailWord_2096883, baseEnd_2096883] using wordTrace_append hprefix tailTrace_2096883
  have hstable : (prefixWord ++ tailWord_2096883).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096883).length < 2 ^ (prefixWord ++ tailWord_2096883).sum := by decide
  have hdescent : baseEnd_2096883 < baseStart_2096883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096945 : List Nat := [1, 2, 2, 3, 2, 2, 1, 3, 5]
def baseStart_2096945 : Nat := 118140960795 + 2096945 * 2 ^ 59
def prefixEnd_2096945 : Nat := 4983230072969 + 3 ^ 40 * 2096945 * 2
def baseEnd_2096945 : Nat := 478551418241068189663925

theorem tailTrace_2096945 : CollatzResearch.WordTrace tailWord_2096945 prefixEnd_2096945 478551418241068189663925 := by
  unfold tailWord_2096945
  simp only [CollatzResearch.WordTrace]
  refine ⟨76481867388133869538948289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50987911592089246359298859 76481867388133869538948289)
  ·
    refine ⟨57361400541100402154211217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76481867388133869538948289 57361400541100402154211217)
    ·
      refine ⟨43021050405825301615658413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57361400541100402154211217 43021050405825301615658413)
      ·
        refine ⟨16132893902184488105871905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43021050405825301615658413 16132893902184488105871905)
        ·
          refine ⟨12099670426638366079403929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16132893902184488105871905 12099670426638366079403929)
          ·
            refine ⟨9074752819978774559552947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12099670426638366079403929 9074752819978774559552947)
            ·
              refine ⟨13612129229968161839329421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9074752819978774559552947 13612129229968161839329421)
              ·
                refine ⟨5104548461238060689748533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13612129229968161839329421 5104548461238060689748533)
                ·
                  refine ⟨478551418241068189663925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5104548461238060689748533 478551418241068189663925)
                  ·
                    rfl

theorem cell21_2096945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 5].length) (baseStart_2096945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2096945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2096945 prefixEnd_2096945 := by exact prefixLift 2096945
  have htrace : WordTrace (prefixWord ++ tailWord_2096945) baseStart_2096945 baseEnd_2096945 := by
    simpa [prefixWord, tailWord_2096945, baseEnd_2096945] using wordTrace_append hprefix tailTrace_2096945
  have hstable : (prefixWord ++ tailWord_2096945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096945).length < 2 ^ (prefixWord ++ tailWord_2096945).sum := by decide
  have hdescent : baseEnd_2096945 < baseStart_2096945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096996 : List Nat := [2, 3, 1, 1, 5, 1, 3, 2, 3]
def baseStart_2096996 : Nat := 118140960795 + 2096996 * 2 ^ 59
def prefixEnd_2096996 : Nat := 4983230072969 + 3 ^ 40 * 2096996 * 2
def baseEnd_2096996 : Nat := 478563057135903434313821

theorem tailTrace_2096996 : CollatzResearch.WordTrace tailWord_2096996 prefixEnd_2096996 478563057135903434313821 := by
  unfold tailWord_2096996
  simp only [CollatzResearch.WordTrace]
  refine ⟨38241863755474552624527421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50989151673966070166036561 38241863755474552624527421)
  ·
    refine ⟨14340698908302957234197783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38241863755474552624527421 14340698908302957234197783)
    ·
      refine ⟨21511048362454435851296675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14340698908302957234197783 21511048362454435851296675)
      ·
        refine ⟨32266572543681653776945013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21511048362454435851296675 32266572543681653776945013)
        ·
          refine ⟨3024991175970155041588595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32266572543681653776945013 3024991175970155041588595)
          ·
            refine ⟨4537486763955232562382893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3024991175970155041588595 4537486763955232562382893)
            ·
              refine ⟨1701557536483212210893585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4537486763955232562382893 1701557536483212210893585)
              ·
                refine ⟨1276168152362409158170189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1701557536483212210893585 1276168152362409158170189)
                ·
                  refine ⟨478563057135903434313821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1276168152362409158170189 478563057135903434313821)
                  ·
                    rfl

theorem cell21_2096996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 2, 3].length) (baseStart_2096996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2096996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2096996 prefixEnd_2096996 := by exact prefixLift 2096996
  have htrace : WordTrace (prefixWord ++ tailWord_2096996) baseStart_2096996 baseEnd_2096996 := by
    simpa [prefixWord, tailWord_2096996, baseEnd_2096996] using wordTrace_append hprefix tailTrace_2096996
  have hstable : (prefixWord ++ tailWord_2096996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096996).length < 2 ^ (prefixWord ++ tailWord_2096996).sum := by decide
  have hdescent : baseEnd_2096996 < baseStart_2096996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097055 : List Nat := [1, 1, 2, 5, 3, 1, 1, 4, 3]
def baseStart_2097055 : Nat := 118140960795 + 2097055 * 2 ^ 59
def prefixEnd_2097055 : Nat := 4983230072969 + 3 ^ 40 * 2097055 * 2
def baseEnd_2097055 : Nat := 478576521739732442830367

theorem tailTrace_2097055 : CollatzResearch.WordTrace tailWord_2097055 prefixEnd_2097055 478576521739732442830367 := by
  unfold tailWord_2097055
  simp only [CollatzResearch.WordTrace]
  refine ⟨76485879417735358325452619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50990586278490238883635079 76485879417735358325452619)
  ·
    refine ⟨114728819126603037488178929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76485879417735358325452619 114728819126603037488178929)
    ·
      refine ⟨86046614344952278116134197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114728819126603037488178929 86046614344952278116134197)
      ·
        refine ⟨8066870094839276073387581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 86046614344952278116134197 8066870094839276073387581)
        ·
          refine ⟨3025076285564728527520343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8066870094839276073387581 3025076285564728527520343)
          ·
            refine ⟨4537614428347092791280515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3025076285564728527520343 4537614428347092791280515)
            ·
              refine ⟨6806421642520639186920773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4537614428347092791280515 6806421642520639186920773)
              ·
                refine ⟨1276204057972619847547645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6806421642520639186920773 1276204057972619847547645)
                ·
                  refine ⟨478576521739732442830367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1276204057972619847547645 478576521739732442830367)
                  ·
                    rfl

theorem cell21_2097055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 4, 3].length) (baseStart_2097055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2097055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2097055 prefixEnd_2097055 := by exact prefixLift 2097055
  have htrace : WordTrace (prefixWord ++ tailWord_2097055) baseStart_2097055 baseEnd_2097055 := by
    simpa [prefixWord, tailWord_2097055, baseEnd_2097055] using wordTrace_append hprefix tailTrace_2097055
  have hstable : (prefixWord ++ tailWord_2097055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097055).length < 2 ^ (prefixWord ++ tailWord_2097055).sum := by decide
  have hdescent : baseEnd_2097055 < baseStart_2097055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097111 : List Nat := [1, 1, 3, 2, 1, 1, 5, 1, 6]
def baseStart_2097111 : Nat := 118140960795 + 2097111 * 2 ^ 59
def prefixEnd_2097111 : Nat := 4983230072969 + 3 ^ 40 * 2097111 * 2
def baseEnd_2097111 : Nat := 478589301702688789896919

theorem tailTrace_2097111 : CollatzResearch.WordTrace tailWord_2097111 prefixEnd_2097111 478589301702688789896919 := by
  unfold tailWord_2097111
  simp only [CollatzResearch.WordTrace]
  refine ⟨76487921905532479889491187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50991947937021653259660791 76487921905532479889491187)
  ·
    refine ⟨114731882858298719834236781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76487921905532479889491187 114731882858298719834236781)
    ·
      refine ⟨43024456071862019937838793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114731882858298719834236781 43024456071862019937838793)
      ·
        refine ⟨32268342053896514953379095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43024456071862019937838793 32268342053896514953379095)
        ·
          refine ⟨48402513080844772430068643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32268342053896514953379095 48402513080844772430068643)
          ·
            refine ⟨72603769621267158645102965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48402513080844772430068643 72603769621267158645102965)
            ·
              refine ⟨6806603401993796122978403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72603769621267158645102965 6806603401993796122978403)
              ·
                refine ⟨10209905102990694184467605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6806603401993796122978403 10209905102990694184467605)
                ·
                  refine ⟨478589301702688789896919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10209905102990694184467605 478589301702688789896919)
                  ·
                    rfl

theorem cell21_2097111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 6].length) (baseStart_2097111 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2097111 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2097111 prefixEnd_2097111 := by exact prefixLift 2097111
  have htrace : WordTrace (prefixWord ++ tailWord_2097111) baseStart_2097111 baseEnd_2097111 := by
    simpa [prefixWord, tailWord_2097111, baseEnd_2097111] using wordTrace_append hprefix tailTrace_2097111
  have hstable : (prefixWord ++ tailWord_2097111).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097111).length < 2 ^ (prefixWord ++ tailWord_2097111).sum := by decide
  have hdescent : baseEnd_2097111 < baseStart_2097111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097114 : List Nat := [3, 1, 1, 2, 5, 1, 2, 1, 5]
def baseStart_2097114 : Nat := 118140960795 + 2097114 * 2 ^ 59
def prefixEnd_2097114 : Nat := 4983230072969 + 3 ^ 40 * 2097114 * 2
def baseEnd_2097114 : Nat := 478589986343561451346913

theorem tailTrace_2097114 : CollatzResearch.WordTrace tailWord_2097114 prefixEnd_2097114 478589986343561451346913 := by
  unfold tailWord_2097114
  simp only [CollatzResearch.WordTrace]
  refine ⟨19122007831130402850462599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50992020883014407601233597 19122007831130402850462599)
  ·
    refine ⟨28683011746695604275693899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19122007831130402850462599 28683011746695604275693899)
    ·
      refine ⟨43024517620043406413540849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28683011746695604275693899 43024517620043406413540849)
      ·
        refine ⟨32268388215032554810155637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43024517620043406413540849 32268388215032554810155637)
        ·
          refine ⟨3025161395159302013452091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32268388215032554810155637 3025161395159302013452091)
          ·
            refine ⟨4537742092738953020178137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3025161395159302013452091 4537742092738953020178137)
            ·
              refine ⟨3403306569554214765133603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4537742092738953020178137 3403306569554214765133603)
              ·
                refine ⟨5104959854331322147700405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3403306569554214765133603 5104959854331322147700405)
                ·
                  refine ⟨478589986343561451346913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5104959854331322147700405 478589986343561451346913)
                  ·
                    rfl

theorem cell21_2097114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 5].length) (baseStart_2097114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2097114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2097114 prefixEnd_2097114 := by exact prefixLift 2097114
  have htrace : WordTrace (prefixWord ++ tailWord_2097114) baseStart_2097114 baseEnd_2097114 := by
    simpa [prefixWord, tailWord_2097114, baseEnd_2097114] using wordTrace_append hprefix tailTrace_2097114
  have hstable : (prefixWord ++ tailWord_2097114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097114).length < 2 ^ (prefixWord ++ tailWord_2097114).sum := by decide
  have hdescent : baseEnd_2097114 < baseStart_2097114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
