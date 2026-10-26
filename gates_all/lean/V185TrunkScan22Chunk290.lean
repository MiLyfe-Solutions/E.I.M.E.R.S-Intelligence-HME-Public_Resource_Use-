import V185TrunkScan22Chunk289

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2585656 : List Nat := [2, 1, 2, 1, 5, 2, 2, 1, 2, 4]
def baseStart_2585656 : Nat := 118140960795 + 2585656 * 2 ^ 59
def prefixEnd_2585656 : Nat := 4983230072969 + 3 ^ 40 * 2585656 * 2
def baseEnd_2585656 : Nat := 885122890121227228472527

theorem tailTrace_2585656 : CollatzResearch.WordTrace tailWord_2585656 prefixEnd_2585656 885122890121227228472527 := by
  unfold tailWord_2585656
  simp only [CollatzResearch.WordTrace]
  refine ⟨47153310960308690866372411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62871081280411587821829881 47153310960308690866372411)
  ·
    refine ⟨70729966440463036299558617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47153310960308690866372411 70729966440463036299558617)
    ·
      refine ⟨53047474830347277224668963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70729966440463036299558617 53047474830347277224668963)
      ·
        refine ⟨79571212245520915837003445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53047474830347277224668963 79571212245520915837003445)
        ·
          refine ⟨7459801148017585859719073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79571212245520915837003445 7459801148017585859719073)
          ·
            refine ⟨5594850861013189394789305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7459801148017585859719073 5594850861013189394789305)
            ·
              refine ⟨4196138145759892046091979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5594850861013189394789305 4196138145759892046091979)
              ·
                refine ⟨6294207218639838069137969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4196138145759892046091979 6294207218639838069137969)
                ·
                  refine ⟨4720655413979878551853477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6294207218639838069137969 4720655413979878551853477)
                  ·
                    refine ⟨885122890121227228472527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4720655413979878551853477 885122890121227228472527)
                    ·
                      rfl

theorem cell22_2585656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 2, 4].length) (baseStart_2585656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2585656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2585656 prefixEnd_2585656 := by exact prefixLift 2585656
  have htrace : WordTrace (prefixWord ++ tailWord_2585656) baseStart_2585656 baseEnd_2585656 := by
    simpa [prefixWord, tailWord_2585656, baseEnd_2585656] using wordTrace_append hprefix tailTrace_2585656
  have hstable : (prefixWord ++ tailWord_2585656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585656).length < 2 ^ (prefixWord ++ tailWord_2585656).sum := by decide
  have hdescent : baseEnd_2585656 < baseStart_2585656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585684 : List Nat := [2, 4, 1, 1, 1, 1, 3, 1, 2, 6]
def baseStart_2585684 : Nat := 118140960795 + 2585684 * 2 ^ 59
def prefixEnd_2585684 : Nat := 4983230072969 + 3 ^ 40 * 2585684 * 2
def baseEnd_2585684 : Nat := 885132475093444488772441

theorem tailTrace_2585684 : CollatzResearch.WordTrace tailWord_2585684 prefixEnd_2585684 885132475093444488772441 := by
  unfold tailWord_2585684
  simp only [CollatzResearch.WordTrace]
  refine ⟨47153821582257971257382053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62871762109677295009842737 47153821582257971257382053)
  ·
    refine ⟨8841341546673369610759135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47153821582257971257382053 8841341546673369610759135)
    ·
      refine ⟨13262012320010054416138703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8841341546673369610759135 13262012320010054416138703)
      ·
        refine ⟨19893018480015081624208055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13262012320010054416138703 19893018480015081624208055)
        ·
          refine ⟨29839527720022622436312083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19893018480015081624208055 29839527720022622436312083)
          ·
            refine ⟨44759291580033933654468125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29839527720022622436312083 44759291580033933654468125)
            ·
              refine ⟨16784734342512725120425547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44759291580033933654468125 16784734342512725120425547)
              ·
                refine ⟨25177101513769087680638321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16784734342512725120425547 25177101513769087680638321)
                ·
                  refine ⟨18882826135326815760478741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25177101513769087680638321 18882826135326815760478741)
                  ·
                    refine ⟨885132475093444488772441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18882826135326815760478741 885132475093444488772441)
                    ·
                      rfl

theorem cell22_2585684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_2585684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2585684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2585684 prefixEnd_2585684 := by exact prefixLift 2585684
  have htrace : WordTrace (prefixWord ++ tailWord_2585684) baseStart_2585684 baseEnd_2585684 := by
    simpa [prefixWord, tailWord_2585684, baseEnd_2585684] using wordTrace_append hprefix tailTrace_2585684
  have hstable : (prefixWord ++ tailWord_2585684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585684).length < 2 ^ (prefixWord ++ tailWord_2585684).sum := by decide
  have hdescent : baseEnd_2585684 < baseStart_2585684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585714 : List Nat := [3, 2, 1, 2, 2, 1, 1, 2, 1, 7]
def baseStart_2585714 : Nat := 118140960795 + 2585714 * 2 ^ 59
def prefixEnd_2585714 : Nat := 4983230072969 + 3 ^ 40 * 2585714 * 2
def baseEnd_2585714 : Nat := 885142744706534410522349

theorem tailTrace_2585714 : CollatzResearch.WordTrace tailWord_2585714 prefixEnd_2585714 885142744706534410522349 := by
  unfold tailWord_2585714
  simp only [CollatzResearch.WordTrace]
  refine ⟨23577184338601814409589049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62872491569604838425570797 23577184338601814409589049)
  ·
    refine ⟨17682888253951360807191787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23577184338601814409589049 17682888253951360807191787)
    ·
      refine ⟨26524332380927041210787681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17682888253951360807191787 26524332380927041210787681)
      ·
        refine ⟨19893249285695280908090761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26524332380927041210787681 19893249285695280908090761)
        ·
          refine ⟨14919936964271460681068071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19893249285695280908090761 14919936964271460681068071)
          ·
            refine ⟨22379905446407191021602107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14919936964271460681068071 22379905446407191021602107)
            ·
              refine ⟨33569858169610786532403161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22379905446407191021602107 33569858169610786532403161)
              ·
                refine ⟨25177393627208089899302371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33569858169610786532403161 25177393627208089899302371)
                ·
                  refine ⟨37766090440812134848953557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25177393627208089899302371 37766090440812134848953557)
                  ·
                    refine ⟨885142744706534410522349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37766090440812134848953557 885142744706534410522349)
                    ·
                      rfl

theorem cell22_2585714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_2585714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2585714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2585714 prefixEnd_2585714 := by exact prefixLift 2585714
  have htrace : WordTrace (prefixWord ++ tailWord_2585714) baseStart_2585714 baseEnd_2585714 := by
    simpa [prefixWord, tailWord_2585714, baseEnd_2585714] using wordTrace_append hprefix tailTrace_2585714
  have hstable : (prefixWord ++ tailWord_2585714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585714).length < 2 ^ (prefixWord ++ tailWord_2585714).sum := by decide
  have hdescent : baseEnd_2585714 < baseStart_2585714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585726 : List Nat := [4, 2, 4, 1, 2, 1, 1, 2, 2, 3]
def baseStart_2585726 : Nat := 118140960795 + 2585726 * 2 ^ 59
def prefixEnd_2585726 : Nat := 4983230072969 + 3 ^ 40 * 2585726 * 2
def baseEnd_2585726 : Nat := 885146852551770379222313

theorem tailTrace_2585726 : CollatzResearch.WordTrace tailWord_2585726 prefixEnd_2585726 885146852551770379222313 := by
  unfold tailWord_2585726
  simp only [CollatzResearch.WordTrace]
  refine ⟨11788646878795472960974129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62872783353575855791862021 11788646878795472960974129)
  ·
    refine ⟨8841485159096604720730597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11788646878795472960974129 8841485159096604720730597)
    ·
      refine ⟨1657778467330613385136987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8841485159096604720730597 1657778467330613385136987)
      ·
        refine ⟨2486667700995920077705481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1657778467330613385136987 2486667700995920077705481)
        ·
          refine ⟨1865000775746940058279111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2486667700995920077705481 1865000775746940058279111)
          ·
            refine ⟨2797501163620410087418667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1865000775746940058279111 2797501163620410087418667)
            ·
              refine ⟨4196251745430615131128001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2797501163620410087418667 4196251745430615131128001)
              ·
                refine ⟨3147188809072961348346001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4196251745430615131128001 3147188809072961348346001)
                ·
                  refine ⟨2360391606804721011259501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3147188809072961348346001 2360391606804721011259501)
                  ·
                    refine ⟨885146852551770379222313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2360391606804721011259501 885146852551770379222313)
                    ·
                      rfl

theorem cell22_2585726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_2585726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2585726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2585726 prefixEnd_2585726 := by exact prefixLift 2585726
  have htrace : WordTrace (prefixWord ++ tailWord_2585726) baseStart_2585726 baseEnd_2585726 := by
    simpa [prefixWord, tailWord_2585726, baseEnd_2585726] using wordTrace_append hprefix tailTrace_2585726
  have hstable : (prefixWord ++ tailWord_2585726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585726).length < 2 ^ (prefixWord ++ tailWord_2585726).sum := by decide
  have hdescent : baseEnd_2585726 < baseStart_2585726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585733 : List Nat := [1, 3, 1, 1, 6, 2, 1, 2, 5]
def baseStart_2585733 : Nat := 118140960795 + 2585733 * 2 ^ 59
def prefixEnd_2585733 : Nat := 4983230072969 + 3 ^ 40 * 2585733 * 2
def baseEnd_2585733 : Nat := 295049749598274898099097

theorem tailTrace_2585733 : CollatzResearch.WordTrace tailWord_2585733 prefixEnd_2585733 295049749598274898099097 := by
  unfold tailWord_2585733
  simp only [CollatzResearch.WordTrace]
  refine ⟨94309430341338423883297853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62872953560892282588865235 94309430341338423883297853)
  ·
    refine ⟨35366036378001908956236695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94309430341338423883297853 35366036378001908956236695)
    ·
      refine ⟨53049054567002863434355043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35366036378001908956236695 53049054567002863434355043)
      ·
        refine ⟨79573581850504295151532565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53049054567002863434355043 79573581850504295151532565)
        ·
          refine ⟨3730011649242388835228089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 79573581850504295151532565 3730011649242388835228089)
          ·
            refine ⟨2797508736931791626421067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3730011649242388835228089 2797508736931791626421067)
            ·
              refine ⟨4196263105397687439631601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2797508736931791626421067 4196263105397687439631601)
              ·
                refine ⟨3147197329048265579723701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4196263105397687439631601 3147197329048265579723701)
                ·
                  refine ⟨295049749598274898099097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3147197329048265579723701 295049749598274898099097)
                  ·
                    rfl

theorem cell22_2585733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 2, 5].length) (baseStart_2585733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2585733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2585733 prefixEnd_2585733 := by exact prefixLift 2585733
  have htrace : WordTrace (prefixWord ++ tailWord_2585733) baseStart_2585733 baseEnd_2585733 := by
    simpa [prefixWord, tailWord_2585733, baseEnd_2585733] using wordTrace_append hprefix tailTrace_2585733
  have hstable : (prefixWord ++ tailWord_2585733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585733).length < 2 ^ (prefixWord ++ tailWord_2585733).sum := by decide
  have hdescent : baseEnd_2585733 < baseStart_2585733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585778 : List Nat := [3, 2, 1, 1, 1, 4, 3, 3, 4]
def baseStart_2585778 : Nat := 118140960795 + 2585778 * 2 ^ 59
def prefixEnd_2585778 : Nat := 4983230072969 + 3 ^ 40 * 2585778 * 2
def baseEnd_2585778 : Nat := 295054884404819858974051

theorem tailTrace_2585778 : CollatzResearch.WordTrace tailWord_2585778 prefixEnd_2585778 295054884404819858974051 := by
  unfold tailWord_2585778
  simp only [CollatzResearch.WordTrace]
  refine ⟨23577767906543849142171497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62874047750783597712457325 23577767906543849142171497)
  ·
    refine ⟨17683325929907886856628623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23577767906543849142171497 17683325929907886856628623)
    ·
      refine ⟨26524988894861830284942935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17683325929907886856628623 26524988894861830284942935)
      ·
        refine ⟨39787483342292745427414403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26524988894861830284942935 39787483342292745427414403)
        ·
          refine ⟨59681225013439118141121605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39787483342292745427414403 59681225013439118141121605)
          ·
            refine ⟨11190229690019834651460301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59681225013439118141121605 11190229690019834651460301)
            ·
              refine ⟨4196336133757437994297613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11190229690019834651460301 4196336133757437994297613)
              ·
                refine ⟨1573626050159039247861605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4196336133757437994297613 1573626050159039247861605)
                ·
                  refine ⟨295054884404819858974051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1573626050159039247861605 295054884404819858974051)
                  ·
                    rfl

theorem cell22_2585778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 3, 4].length) (baseStart_2585778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2585778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2585778 prefixEnd_2585778 := by exact prefixLift 2585778
  have htrace : WordTrace (prefixWord ++ tailWord_2585778) baseStart_2585778 baseEnd_2585778 := by
    simpa [prefixWord, tailWord_2585778, baseEnd_2585778] using wordTrace_append hprefix tailTrace_2585778
  have hstable : (prefixWord ++ tailWord_2585778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585778).length < 2 ^ (prefixWord ++ tailWord_2585778).sum := by decide
  have hdescent : baseEnd_2585778 < baseStart_2585778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585789 : List Nat := [1, 4, 1, 2, 1, 1, 12]
def baseStart_2585789 : Nat := 118140960795 + 2585789 * 2 ^ 59
def prefixEnd_2585789 : Nat := 4983230072969 + 3 ^ 40 * 2585789 * 2
def baseEnd_2585789 : Nat := 32784015508861452403597

theorem tailTrace_2585789 : CollatzResearch.WordTrace tailWord_2585789 prefixEnd_2585789 32784015508861452403597 := by
  unfold tailWord_2585789
  simp only [CollatzResearch.WordTrace]
  refine ⟨94311472829135545447336421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62874315219423696964890947 94311472829135545447336421)
  ·
    refine ⟨17683401155462914771375579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94311472829135545447336421 17683401155462914771375579)
    ·
      refine ⟨26525101733194372157063369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17683401155462914771375579 26525101733194372157063369)
      ·
        refine ⟨19893826299895779117797527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26525101733194372157063369 19893826299895779117797527)
        ·
          refine ⟨29840739449843668676696291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19893826299895779117797527 29840739449843668676696291)
          ·
            refine ⟨44761109174765503015044437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29840739449843668676696291 44761109174765503015044437)
            ·
              refine ⟨32784015508861452403597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 44761109174765503015044437 32784015508861452403597)
              ·
                rfl

theorem cell22_2585789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 12].length) (baseStart_2585789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2585789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2585789 prefixEnd_2585789 := by exact prefixLift 2585789
  have htrace : WordTrace (prefixWord ++ tailWord_2585789) baseStart_2585789 baseEnd_2585789 := by
    simpa [prefixWord, tailWord_2585789, baseEnd_2585789] using wordTrace_append hprefix tailTrace_2585789
  have hstable : (prefixWord ++ tailWord_2585789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585789).length < 2 ^ (prefixWord ++ tailWord_2585789).sum := by decide
  have hdescent : baseEnd_2585789 < baseStart_2585789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585814 : List Nat := [5, 2, 1, 2, 3, 1, 1, 2, 1, 4]
def baseStart_2585814 : Nat := 118140960795 + 2585814 * 2 ^ 59
def prefixEnd_2585814 : Nat := 4983230072969 + 3 ^ 40 * 2585814 * 2
def baseEnd_2585814 : Nat := 885176976750167483022043

theorem tailTrace_2585814 : CollatzResearch.WordTrace tailWord_2585814 prefixEnd_2585814 885176976750167483022043 := by
  unfold tailWord_2585814
  simp only [CollatzResearch.WordTrace]
  refine ⟨5894524040877810919812281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62874923102696649811330997 5894524040877810919812281)
  ·
    refine ⟨4420893030658358189859211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5894524040877810919812281 4420893030658358189859211)
    ·
      refine ⟨6631339545987537284788817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4420893030658358189859211 6631339545987537284788817)
      ·
        refine ⟨4973504659490652963591613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6631339545987537284788817 4973504659490652963591613)
        ·
          refine ⟨1865064247308994861346855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4973504659490652963591613 1865064247308994861346855)
          ·
            refine ⟨2797596370963492292020283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1865064247308994861346855 2797596370963492292020283)
            ·
              refine ⟨4196394556445238438030425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2797596370963492292020283 4196394556445238438030425)
              ·
                refine ⟨3147295917333928828522819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4196394556445238438030425 3147295917333928828522819)
                ·
                  refine ⟨4720943876000893242784229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3147295917333928828522819 4720943876000893242784229)
                  ·
                    refine ⟨885176976750167483022043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4720943876000893242784229 885176976750167483022043)
                    ·
                      rfl

theorem cell22_2585814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_2585814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2585814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2585814 prefixEnd_2585814 := by exact prefixLift 2585814
  have htrace : WordTrace (prefixWord ++ tailWord_2585814) baseStart_2585814 baseEnd_2585814 := by
    simpa [prefixWord, tailWord_2585814, baseEnd_2585814] using wordTrace_append hprefix tailTrace_2585814
  have hstable : (prefixWord ++ tailWord_2585814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585814).length < 2 ^ (prefixWord ++ tailWord_2585814).sum := by decide
  have hdescent : baseEnd_2585814 < baseStart_2585814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585855 : List Nat := [1, 1, 2, 2, 1, 6, 1, 4, 1, 3]
def baseStart_2585855 : Nat := 118140960795 + 2585855 * 2 ^ 59
def prefixEnd_2585855 : Nat := 4983230072969 + 3 ^ 40 * 2585855 * 2
def baseEnd_2585855 : Nat := 885191011888057042746917

theorem tailTrace_2585855 : CollatzResearch.WordTrace tailWord_2585855 prefixEnd_2585855 885191011888057042746917 := by
  unfold tailWord_2585855
  simp only [CollatzResearch.WordTrace]
  refine ⟨94313880046896438719239019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62875920031264292479492679 94313880046896438719239019)
  ·
    refine ⟨141470820070344658078858529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94313880046896438719239019 141470820070344658078858529)
    ·
      refine ⟨106103115052758493559143897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141470820070344658078858529 106103115052758493559143897)
      ·
        refine ⟨79577336289568870169357923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106103115052758493559143897 79577336289568870169357923)
        ·
          refine ⟨119366004434353305254036885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79577336289568870169357923 119366004434353305254036885)
          ·
            refine ⟨5595281457860311183782979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 119366004434353305254036885 5595281457860311183782979)
            ·
              refine ⟨8392922186790466775674469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5595281457860311183782979 8392922186790466775674469)
              ·
                refine ⟨1573672910023212520438963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8392922186790466775674469 1573672910023212520438963)
                ·
                  refine ⟨2360509365034818780658445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1573672910023212520438963 2360509365034818780658445)
                  ·
                    refine ⟨885191011888057042746917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2360509365034818780658445 885191011888057042746917)
                    ·
                      rfl

theorem cell22_2585855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 4, 1, 3].length) (baseStart_2585855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2585855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2585855 prefixEnd_2585855 := by exact prefixLift 2585855
  have htrace : WordTrace (prefixWord ++ tailWord_2585855) baseStart_2585855 baseEnd_2585855 := by
    simpa [prefixWord, tailWord_2585855, baseEnd_2585855] using wordTrace_append hprefix tailTrace_2585855
  have hstable : (prefixWord ++ tailWord_2585855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585855).length < 2 ^ (prefixWord ++ tailWord_2585855).sum := by decide
  have hdescent : baseEnd_2585855 < baseStart_2585855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585960 : List Nat := [2, 1, 4, 2, 3, 1, 1, 2, 2, 4]
def baseStart_2585960 : Nat := 118140960795 + 2585960 * 2 ^ 59
def prefixEnd_2585960 : Nat := 4983230072969 + 3 ^ 40 * 2585960 * 2
def baseEnd_2585960 : Nat := 885226955533871768871595

theorem tailTrace_2585960 : CollatzResearch.WordTrace tailWord_2585960 prefixEnd_2585960 885226955533871768871595 := by
  unfold tailWord_2585960
  simp only [CollatzResearch.WordTrace]
  refine ⟨47158854855758020825905667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62878473141010694434540889 47158854855758020825905667)
  ·
    refine ⟨70738282283637031238858501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47158854855758020825905667 70738282283637031238858501)
    ·
      refine ⟨13263427928181943357285969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70738282283637031238858501 13263427928181943357285969)
      ·
        refine ⟨9947570946136457517964477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13263427928181943357285969 9947570946136457517964477)
        ·
          refine ⟨3730339104801171569236679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9947570946136457517964477 3730339104801171569236679)
          ·
            refine ⟨5595508657201757353855019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3730339104801171569236679 5595508657201757353855019)
            ·
              refine ⟨8393262985802636030782529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5595508657201757353855019 8393262985802636030782529)
              ·
                refine ⟨6294947239351977023086897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8393262985802636030782529 6294947239351977023086897)
                ·
                  refine ⟨4721210429513982767315173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6294947239351977023086897 4721210429513982767315173)
                  ·
                    refine ⟨885226955533871768871595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4721210429513982767315173 885226955533871768871595)
                    ·
                      rfl

theorem cell22_2585960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_2585960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2585960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2585960 prefixEnd_2585960 := by exact prefixLift 2585960
  have htrace : WordTrace (prefixWord ++ tailWord_2585960) baseStart_2585960 baseEnd_2585960 := by
    simpa [prefixWord, tailWord_2585960, baseEnd_2585960] using wordTrace_append hprefix tailTrace_2585960
  have hstable : (prefixWord ++ tailWord_2585960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585960).length < 2 ^ (prefixWord ++ tailWord_2585960).sum := by decide
  have hdescent : baseEnd_2585960 < baseStart_2585960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586001 : List Nat := [1, 2, 2, 1, 1, 1, 2, 4, 1, 7]
def baseStart_2586001 : Nat := 118140960795 + 2586001 * 2 ^ 59
def prefixEnd_2586001 : Nat := 4983230072969 + 3 ^ 40 * 2586001 * 2
def baseEnd_2586001 : Nat := 885240990671761328596469

theorem tailTrace_2586001 : CollatzResearch.WordTrace tailWord_2586001 prefixEnd_2586001 885240990671761328596469 := by
  unfold tailWord_2586001
  simp only [CollatzResearch.WordTrace]
  refine ⟨94319205104367505654053857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62879470069578337102702571 94319205104367505654053857)
  ·
    refine ⟨70739403828275629240540393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94319205104367505654053857 70739403828275629240540393)
    ·
      refine ⟨53054552871206721930405295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70739403828275629240540393 53054552871206721930405295)
      ·
        refine ⟨79581829306810082895607943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53054552871206721930405295 79581829306810082895607943)
        ·
          refine ⟨119372743960215124343411915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79581829306810082895607943 119372743960215124343411915)
          ·
            refine ⟨179059115940322686515117873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119372743960215124343411915 179059115940322686515117873)
            ·
              refine ⟨134294336955242014886338405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179059115940322686515117873 134294336955242014886338405)
              ·
                refine ⟨25180188179107877791188451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 134294336955242014886338405 25180188179107877791188451)
                ·
                  refine ⟨37770282268661816686782677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25180188179107877791188451 37770282268661816686782677)
                  ·
                    refine ⟨885240990671761328596469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37770282268661816686782677 885240990671761328596469)
                    ·
                      rfl

theorem cell22_2586001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_2586001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2586001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2586001 prefixEnd_2586001 := by exact prefixLift 2586001
  have htrace : WordTrace (prefixWord ++ tailWord_2586001) baseStart_2586001 baseEnd_2586001 := by
    simpa [prefixWord, tailWord_2586001, baseEnd_2586001] using wordTrace_append hprefix tailTrace_2586001
  have hstable : (prefixWord ++ tailWord_2586001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586001).length < 2 ^ (prefixWord ++ tailWord_2586001).sum := by decide
  have hdescent : baseEnd_2586001 < baseStart_2586001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586031 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 10]
def baseStart_2586031 : Nat := 118140960795 + 2586031 * 2 ^ 59
def prefixEnd_2586031 : Nat := 4983230072969 + 3 ^ 40 * 2586031 * 2
def baseEnd_2586031 : Nat := 295083753428283750115459

theorem tailTrace_2586031 : CollatzResearch.WordTrace tailWord_2586031 prefixEnd_2586031 295083753428283750115459 := by
  unfold tailWord_2586031
  simp only [CollatzResearch.WordTrace]
  refine ⟨94320299294258820777645947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62880199529505880518430631 94320299294258820777645947)
  ·
    refine ⟨141480448941388231166468921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94320299294258820777645947 141480448941388231166468921)
    ·
      refine ⟨106110336706041173374851691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141480448941388231166468921 106110336706041173374851691)
      ·
        refine ⟨159165505059061760062277537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106110336706041173374851691 159165505059061760062277537)
        ·
          refine ⟨119374128794296320046708153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159165505059061760062277537 119374128794296320046708153)
          ·
            refine ⟨89530596595722240035031115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119374128794296320046708153 89530596595722240035031115)
            ·
              refine ⟨134295894893583360052546673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89530596595722240035031115 134295894893583360052546673)
              ·
                refine ⟨100721921170187520039410005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134295894893583360052546673 100721921170187520039410005)
                ·
                  refine ⟨295083753428283750115459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 100721921170187520039410005 295083753428283750115459)
                  ·
                    rfl

theorem cell22_2586031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 10].length) (baseStart_2586031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2586031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2586031 prefixEnd_2586031 := by exact prefixLift 2586031
  have htrace : WordTrace (prefixWord ++ tailWord_2586031) baseStart_2586031 baseEnd_2586031 := by
    simpa [prefixWord, tailWord_2586031, baseEnd_2586031] using wordTrace_append hprefix tailTrace_2586031
  have hstable : (prefixWord ++ tailWord_2586031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586031).length < 2 ^ (prefixWord ++ tailWord_2586031).sum := by decide
  have hdescent : baseEnd_2586031 < baseStart_2586031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586033 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 5, 4]
def baseStart_2586033 : Nat := 118140960795 + 2586033 * 2 ^ 59
def prefixEnd_2586033 : Nat := 4983230072969 + 3 ^ 40 * 2586033 * 2
def baseEnd_2586033 : Nat := 885251944925723911796371

theorem tailTrace_2586033 : CollatzResearch.WordTrace tailWord_2586033 prefixEnd_2586033 885251944925723911796371 := by
  unfold tailWord_2586033
  simp only [CollatzResearch.WordTrace]
  refine ⟨94320372240251575119218753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62880248160167716746145835 94320372240251575119218753)
  ·
    refine ⟨70740279180188681339414065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94320372240251575119218753 70740279180188681339414065)
    ·
      refine ⟨53055209385141511004560549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70740279180188681339414065 53055209385141511004560549)
      ·
        refine ⟨9947851759714033313355103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53055209385141511004560549 9947851759714033313355103)
        ·
          refine ⟨14921777639571049970032655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9947851759714033313355103 14921777639571049970032655)
          ·
            refine ⟨22382666459356574955048983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14921777639571049970032655 22382666459356574955048983)
            ·
              refine ⟨33573999689034862432573475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22382666459356574955048983 33573999689034862432573475)
              ·
                refine ⟨50360999533552293648860213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33573999689034862432573475 50360999533552293648860213)
                ·
                  refine ⟨4721343706270527529580645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50360999533552293648860213 4721343706270527529580645)
                  ·
                    refine ⟨885251944925723911796371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4721343706270527529580645 885251944925723911796371)
                    ·
                      rfl

theorem cell22_2586033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 5, 4].length) (baseStart_2586033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2586033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2586033 prefixEnd_2586033 := by exact prefixLift 2586033
  have htrace : WordTrace (prefixWord ++ tailWord_2586033) baseStart_2586033 baseEnd_2586033 := by
    simpa [prefixWord, tailWord_2586033, baseEnd_2586033] using wordTrace_append hprefix tailTrace_2586033
  have hstable : (prefixWord ++ tailWord_2586033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586033).length < 2 ^ (prefixWord ++ tailWord_2586033).sum := by decide
  have hdescent : baseEnd_2586033 < baseStart_2586033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586063 : List Nat := [1, 1, 2, 1, 1, 4, 4, 2, 1, 5]
def baseStart_2586063 : Nat := 118140960795 + 2586063 * 2 ^ 59
def prefixEnd_2586063 : Nat := 4983230072969 + 3 ^ 40 * 2586063 * 2
def baseEnd_2586063 : Nat := 885262214538813833546279

theorem tailTrace_2586063 : CollatzResearch.WordTrace tailWord_2586063 prefixEnd_2586063 885262214538813833546279 := by
  unfold tailWord_2586063
  simp only [CollatzResearch.WordTrace]
  refine ⟨94321466430142890242810843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62880977620095260161873895 94321466430142890242810843)
  ·
    refine ⟨141482199645214335364216265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94321466430142890242810843 141482199645214335364216265)
    ·
      refine ⟨106111649733910751523162199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141482199645214335364216265 106111649733910751523162199)
      ·
        refine ⟨159167474600866127284743299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106111649733910751523162199 159167474600866127284743299)
        ·
          refine ⟨238751211901299190927114949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159167474600866127284743299 238751211901299190927114949)
          ·
            refine ⟨44765852231493598298834053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 238751211901299190927114949 44765852231493598298834053)
            ·
              refine ⟨8393597293405049681031385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44765852231493598298834053 8393597293405049681031385)
              ·
                refine ⟨6295197970053787260773539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8393597293405049681031385 6295197970053787260773539)
                ·
                  refine ⟨9442796955080680891160309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6295197970053787260773539 9442796955080680891160309)
                  ·
                    refine ⟨885262214538813833546279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9442796955080680891160309 885262214538813833546279)
                    ·
                      rfl

theorem cell22_2586063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 5].length) (baseStart_2586063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2586063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2586063 prefixEnd_2586063 := by exact prefixLift 2586063
  have htrace : WordTrace (prefixWord ++ tailWord_2586063) baseStart_2586063 baseEnd_2586063 := by
    simpa [prefixWord, tailWord_2586063, baseEnd_2586063] using wordTrace_append hprefix tailTrace_2586063
  have hstable : (prefixWord ++ tailWord_2586063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586063).length < 2 ^ (prefixWord ++ tailWord_2586063).sum := by decide
  have hdescent : baseEnd_2586063 < baseStart_2586063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586080 : List Nat := [2, 1, 1, 3, 1, 1, 2, 6, 2, 3]
def baseStart_2586080 : Nat := 118140960795 + 2586080 * 2 ^ 59
def prefixEnd_2586080 : Nat := 4983230072969 + 3 ^ 40 * 2586080 * 2
def baseEnd_2586080 : Nat := 885268033986231455871227

theorem tailTrace_2586080 : CollatzResearch.WordTrace tailWord_2586080 prefixEnd_2586080 885268033986231455871227 := by
  unfold tailWord_2586080
  simp only [CollatzResearch.WordTrace]
  refine ⟨47161043235540651073089847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62881390980720868097453129 47161043235540651073089847)
  ·
    refine ⟨70741564853310976609634771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47161043235540651073089847 70741564853310976609634771)
    ·
      refine ⟨106112347279966464914452157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70741564853310976609634771 106112347279966464914452157)
      ·
        refine ⟨39792130229987424342919559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106112347279966464914452157 39792130229987424342919559)
        ·
          refine ⟨59688195344981136514379339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39792130229987424342919559 59688195344981136514379339)
          ·
            refine ⟨89532293017471704771569009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59688195344981136514379339 89532293017471704771569009)
            ·
              refine ⟨67149219763103778578676757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89532293017471704771569009 67149219763103778578676757)
              ·
                refine ⟨3147619676395489620875473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67149219763103778578676757 3147619676395489620875473)
                ·
                  refine ⟨2360714757296617215656605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3147619676395489620875473 2360714757296617215656605)
                  ·
                    refine ⟨885268033986231455871227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2360714757296617215656605 885268033986231455871227)
                    ·
                      rfl

theorem cell22_2586080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 6, 2, 3].length) (baseStart_2586080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2586080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2586080 prefixEnd_2586080 := by exact prefixLift 2586080
  have htrace : WordTrace (prefixWord ++ tailWord_2586080) baseStart_2586080 baseEnd_2586080 := by
    simpa [prefixWord, tailWord_2586080, baseEnd_2586080] using wordTrace_append hprefix tailTrace_2586080
  have hstable : (prefixWord ++ tailWord_2586080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586080).length < 2 ^ (prefixWord ++ tailWord_2586080).sum := by decide
  have hdescent : baseEnd_2586080 < baseStart_2586080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586116 : List Nat := [2, 3, 2, 3, 3, 1, 1, 3, 4]
def baseStart_2586116 : Nat := 118140960795 + 2586116 * 2 ^ 59
def prefixEnd_2586116 : Nat := 4983230072969 + 3 ^ 40 * 2586116 * 2
def baseEnd_2586116 : Nat := 295093452507313120657039

theorem tailTrace_2586116 : CollatzResearch.WordTrace tailWord_2586116 prefixEnd_2586116 295093452507313120657039 := by
  unfold tailWord_2586116
  simp only [CollatzResearch.WordTrace]
  refine ⟨47161699749475440147245101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62882266332633920196326801 47161699749475440147245101)
  ·
    refine ⟨17685637406053290055216913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47161699749475440147245101 17685637406053290055216913)
    ·
      refine ⟨13264228054539967541412685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17685637406053290055216913 13264228054539967541412685)
      ·
        refine ⟨4974085520452487828029757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13264228054539967541412685 4974085520452487828029757)
        ·
          refine ⟨1865282070169682935511159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4974085520452487828029757 1865282070169682935511159)
          ·
            refine ⟨2797923105254524403266739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1865282070169682935511159 2797923105254524403266739)
            ·
              refine ⟨4196884657881786604900109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2797923105254524403266739 4196884657881786604900109)
              ·
                refine ⟨1573831746705669976837541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4196884657881786604900109 1573831746705669976837541)
                ·
                  refine ⟨295093452507313120657039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1573831746705669976837541 295093452507313120657039)
                  ·
                    rfl

theorem cell22_2586116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 3, 4].length) (baseStart_2586116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2586116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2586116 prefixEnd_2586116 := by exact prefixLift 2586116
  have htrace : WordTrace (prefixWord ++ tailWord_2586116) baseStart_2586116 baseEnd_2586116 := by
    simpa [prefixWord, tailWord_2586116, baseEnd_2586116] using wordTrace_append hprefix tailTrace_2586116
  have hstable : (prefixWord ++ tailWord_2586116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586116).length < 2 ^ (prefixWord ++ tailWord_2586116).sum := by decide
  have hdescent : baseEnd_2586116 < baseStart_2586116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586185 : List Nat := [1, 2, 1, 1, 2, 2, 1, 7, 1, 4]
def baseStart_2586185 : Nat := 118140960795 + 2586185 * 2 ^ 59
def prefixEnd_2586185 : Nat := 4983230072969 + 3 ^ 40 * 2586185 * 2
def baseEnd_2586185 : Nat := 885303977632046181995905

theorem tailTrace_2586185 : CollatzResearch.WordTrace tailWord_2586185 prefixEnd_2586185 885303977632046181995905 := by
  unfold tailWord_2586185
  simp only [CollatzResearch.WordTrace]
  refine ⟨94325916135700905078752009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62883944090467270052501339 94325916135700905078752009)
  ·
    refine ⟨70744437101775678809064007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94325916135700905078752009 70744437101775678809064007)
    ·
      refine ⟨106116655652663518213596011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70744437101775678809064007 106116655652663518213596011)
      ·
        refine ⟨159174983478995277320394017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106116655652663518213596011 159174983478995277320394017)
        ·
          refine ⟨119381237609246457990295513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159174983478995277320394017 119381237609246457990295513)
          ·
            refine ⟨89535928206934843492721635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119381237609246457990295513 89535928206934843492721635)
            ·
              refine ⟨134303892310402265239082453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89535928206934843492721635 134303892310402265239082453)
              ·
                refine ⟨3147747476025053091540995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 134303892310402265239082453 3147747476025053091540995)
                ·
                  refine ⟨4721621214037579637311493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3147747476025053091540995 4721621214037579637311493)
                  ·
                    refine ⟨885303977632046181995905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4721621214037579637311493 885303977632046181995905)
                    ·
                      rfl

theorem cell22_2586185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 7, 1, 4].length) (baseStart_2586185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2586185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2586185 prefixEnd_2586185 := by exact prefixLift 2586185
  have htrace : WordTrace (prefixWord ++ tailWord_2586185) baseStart_2586185 baseEnd_2586185 := by
    simpa [prefixWord, tailWord_2586185, baseEnd_2586185] using wordTrace_append hprefix tailTrace_2586185
  have hstable : (prefixWord ++ tailWord_2586185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586185).length < 2 ^ (prefixWord ++ tailWord_2586185).sum := by decide
  have hdescent : baseEnd_2586185 < baseStart_2586185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586189 : List Nat := [1, 6, 1, 1, 3, 1, 2, 2, 5]
def baseStart_2586189 : Nat := 118140960795 + 2586189 * 2 ^ 59
def prefixEnd_2586189 : Nat := 4983230072969 + 3 ^ 40 * 2586189 * 2
def baseEnd_2586189 : Nat := 295101782304597168298631

theorem tailTrace_2586189 : CollatzResearch.WordTrace tailWord_2586189 prefixEnd_2586189 295101782304597168298631 := by
  unfold tailWord_2586189
  simp only [CollatzResearch.WordTrace]
  refine ⟨94326062027686413761897621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62884041351790942507931747 94326062027686413761897621)
  ·
    refine ⟨4421534157547800645088951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 94326062027686413761897621 4421534157547800645088951)
    ·
      refine ⟨6632301236321700967633427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4421534157547800645088951 6632301236321700967633427)
      ·
        refine ⟨9948451854482551451450141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6632301236321700967633427 9948451854482551451450141)
        ·
          refine ⟨3730669445430956794293803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9948451854482551451450141 3730669445430956794293803)
          ·
            refine ⟨5596004168146435191440705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3730669445430956794293803 5596004168146435191440705)
            ·
              refine ⟨4197003126109826393580529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5596004168146435191440705 4197003126109826393580529)
              ·
                refine ⟨3147752344582369795185397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4197003126109826393580529 3147752344582369795185397)
                ·
                  refine ⟨295101782304597168298631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3147752344582369795185397 295101782304597168298631)
                  ·
                    rfl

theorem cell22_2586189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_2586189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2586189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2586189 prefixEnd_2586189 := by exact prefixLift 2586189
  have htrace : WordTrace (prefixWord ++ tailWord_2586189) baseStart_2586189 baseEnd_2586189 := by
    simpa [prefixWord, tailWord_2586189, baseEnd_2586189] using wordTrace_append hprefix tailTrace_2586189
  have hstable : (prefixWord ++ tailWord_2586189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586189).length < 2 ^ (prefixWord ++ tailWord_2586189).sum := by decide
  have hdescent : baseEnd_2586189 < baseStart_2586189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586215 : List Nat := [1, 1, 5, 1, 1, 1, 3, 3, 1, 5]
def baseStart_2586215 : Nat := 118140960795 + 2586215 * 2 ^ 59
def prefixEnd_2586215 : Nat := 4983230072969 + 3 ^ 40 * 2586215 * 2
def baseEnd_2586215 : Nat := 885314247245136103745813

theorem tailTrace_2586215 : CollatzResearch.WordTrace tailWord_2586215 prefixEnd_2586215 885314247245136103745813 := by
  unfold tailWord_2586215
  simp only [CollatzResearch.WordTrace]
  refine ⟨94327010325592220202344099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62884673550394813468229399 94327010325592220202344099)
  ·
    refine ⟨141490515488388330303516149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94327010325592220202344099 141490515488388330303516149)
    ·
      refine ⟨13264735827036405965954639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 141490515488388330303516149 13264735827036405965954639)
      ·
        refine ⟨19897103740554608948931959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13264735827036405965954639 19897103740554608948931959)
        ·
          refine ⟨29845655610831913423397939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19897103740554608948931959 29845655610831913423397939)
          ·
            refine ⟨44768483416247870135096909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29845655610831913423397939 44768483416247870135096909)
            ·
              refine ⟨16788181281092951300661341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44768483416247870135096909 16788181281092951300661341)
              ·
                refine ⟨6295567980409856737748003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16788181281092951300661341 6295567980409856737748003)
                ·
                  refine ⟨9443351970614785106622005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6295567980409856737748003 9443351970614785106622005)
                  ·
                    refine ⟨885314247245136103745813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9443351970614785106622005 885314247245136103745813)
                    ·
                      rfl

theorem cell22_2586215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_2586215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2586215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2586215 prefixEnd_2586215 := by exact prefixLift 2586215
  have htrace : WordTrace (prefixWord ++ tailWord_2586215) baseStart_2586215 baseEnd_2586215 := by
    simpa [prefixWord, tailWord_2586215, baseEnd_2586215] using wordTrace_append hprefix tailTrace_2586215
  have hstable : (prefixWord ++ tailWord_2586215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586215).length < 2 ^ (prefixWord ++ tailWord_2586215).sum := by decide
  have hdescent : baseEnd_2586215 < baseStart_2586215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586277 : List Nat := [1, 3, 1, 2, 1, 2, 4, 2, 3, 3]
def baseStart_2586277 : Nat := 118140960795 + 2586277 * 2 ^ 59
def prefixEnd_2586277 : Nat := 4983230072969 + 3 ^ 40 * 2586277 * 2
def baseEnd_2586277 : Nat := 885335471112188608695623

theorem tailTrace_2586277 : CollatzResearch.WordTrace tailWord_2586277 prefixEnd_2586277 885335471112188608695623 := by
  unfold tailWord_2586277
  simp only [CollatzResearch.WordTrace]
  refine ⟨94329271651367604791101085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62886181100911736527400723 94329271651367604791101085)
  ·
    refine ⟨35373476869262851796662907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94329271651367604791101085 35373476869262851796662907)
    ·
      refine ⟨53060215303894277694994361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35373476869262851796662907 53060215303894277694994361)
      ·
        refine ⟨39795161477920708271245771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53060215303894277694994361 39795161477920708271245771)
        ·
          refine ⟨59692742216881062406868657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39795161477920708271245771 59692742216881062406868657)
          ·
            refine ⟨44769556662660796805151493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59692742216881062406868657 44769556662660796805151493)
            ·
              refine ⟨8394291874248899400965905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44769556662660796805151493 8394291874248899400965905)
              ·
                refine ⟨6295718905686674550724429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8394291874248899400965905 6295718905686674550724429)
                ·
                  refine ⟨2360894589632502956521661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6295718905686674550724429 2360894589632502956521661)
                  ·
                    refine ⟨885335471112188608695623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2360894589632502956521661 885335471112188608695623)
                    ·
                      rfl

theorem cell22_2586277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 3, 3].length) (baseStart_2586277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2586277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2586277 prefixEnd_2586277 := by exact prefixLift 2586277
  have htrace : WordTrace (prefixWord ++ tailWord_2586277) baseStart_2586277 baseEnd_2586277 := by
    simpa [prefixWord, tailWord_2586277, baseEnd_2586277] using wordTrace_append hprefix tailTrace_2586277
  have hstable : (prefixWord ++ tailWord_2586277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586277).length < 2 ^ (prefixWord ++ tailWord_2586277).sum := by decide
  have hdescent : baseEnd_2586277 < baseStart_2586277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586290 : List Nat := [3, 2, 1, 1, 1, 2, 3, 2, 7]
def baseStart_2586290 : Nat := 118140960795 + 2586290 * 2 ^ 59
def prefixEnd_2586290 : Nat := 4983230072969 + 3 ^ 40 * 2586290 * 2
def baseEnd_2586290 : Nat := 295113307092620302706861

theorem tailTrace_2586290 : CollatzResearch.WordTrace tailWord_2586290 prefixEnd_2586290 295113307092620302706861 := by
  unfold tailWord_2586290
  simp only [CollatzResearch.WordTrace]
  refine ⟨23582436450080127002831081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62886497200213672007549549 23582436450080127002831081)
  ·
    refine ⟨17686827337560095252123311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23582436450080127002831081 17686827337560095252123311)
    ·
      refine ⟨26530241006340142878184967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17686827337560095252123311 26530241006340142878184967)
      ·
        refine ⟨39795361509510214317277451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26530241006340142878184967 39795361509510214317277451)
        ·
          refine ⟨59693042264265321475916177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39795361509510214317277451 59693042264265321475916177)
          ·
            refine ⟨44769781698198991106937133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59693042264265321475916177 44769781698198991106937133)
            ·
              refine ⟨16788668136824621665101425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44769781698198991106937133 16788668136824621665101425)
              ·
                refine ⟨12591501102618466248826069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16788668136824621665101425 12591501102618466248826069)
                ·
                  refine ⟨295113307092620302706861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12591501102618466248826069 295113307092620302706861)
                  ·
                    rfl

theorem cell22_2586290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_2586290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2586290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2586290 prefixEnd_2586290 := by exact prefixLift 2586290
  have htrace : WordTrace (prefixWord ++ tailWord_2586290) baseStart_2586290 baseEnd_2586290 := by
    simpa [prefixWord, tailWord_2586290, baseEnd_2586290] using wordTrace_append hprefix tailTrace_2586290
  have hstable : (prefixWord ++ tailWord_2586290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586290).length < 2 ^ (prefixWord ++ tailWord_2586290).sum := by decide
  have hdescent : baseEnd_2586290 < baseStart_2586290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586311 : List Nat := [1, 1, 4, 1, 1, 1, 7, 2, 1, 3]
def baseStart_2586311 : Nat := 118140960795 + 2586311 * 2 ^ 59
def prefixEnd_2586311 : Nat := 4983230072969 + 3 ^ 40 * 2586311 * 2
def baseEnd_2586311 : Nat := 885347110007023853345519

theorem tailTrace_2586311 : CollatzResearch.WordTrace tailWord_2586311 prefixEnd_2586311 885347110007023853345519 := by
  unfold tailWord_2586311
  simp only [CollatzResearch.WordTrace]
  refine ⟨94330511733244428597838787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62887007822162952398559191 94330511733244428597838787)
  ·
    refine ⟨141495767599866642896758181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94330511733244428597838787 141495767599866642896758181)
    ·
      refine ⟨26530456424974995543142159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141495767599866642896758181 26530456424974995543142159)
      ·
        refine ⟨39795684637462493314713239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26530456424974995543142159 39795684637462493314713239)
        ·
          refine ⟨59693526956193739972069859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39795684637462493314713239 59693526956193739972069859)
          ·
            refine ⟨89540290434290609958104789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59693526956193739972069859 89540290434290609958104789)
            ·
              refine ⟨2098600557053686170893081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 89540290434290609958104789 2098600557053686170893081)
              ·
                refine ⟨1573950417790264628169811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2098600557053686170893081 1573950417790264628169811)
                ·
                  refine ⟨2360925626685396942254717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1573950417790264628169811 2360925626685396942254717)
                  ·
                    refine ⟨885347110007023853345519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2360925626685396942254717 885347110007023853345519)
                    ·
                      rfl

theorem cell22_2586311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 2, 1, 3].length) (baseStart_2586311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2586311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2586311 prefixEnd_2586311 := by exact prefixLift 2586311
  have htrace : WordTrace (prefixWord ++ tailWord_2586311) baseStart_2586311 baseEnd_2586311 := by
    simpa [prefixWord, tailWord_2586311, baseEnd_2586311] using wordTrace_append hprefix tailTrace_2586311
  have hstable : (prefixWord ++ tailWord_2586311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586311).length < 2 ^ (prefixWord ++ tailWord_2586311).sum := by decide
  have hdescent : baseEnd_2586311 < baseStart_2586311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586324 : List Nat := [2, 4, 1, 3, 1, 2, 1, 3, 5]
def baseStart_2586324 : Nat := 118140960795 + 2586324 * 2 ^ 59
def prefixEnd_2586324 : Nat := 4983230072969 + 3 ^ 40 * 2586324 * 2
def baseEnd_2586324 : Nat := 295117186724232050923493

theorem tailTrace_2586324 : CollatzResearch.WordTrace tailWord_2586324 prefixEnd_2586324 295117186724232050923493 := by
  unfold tailWord_2586324
  simp only [CollatzResearch.WordTrace]
  refine ⟨47165492941098665909031013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62887323921464887878708017 47165492941098665909031013)
  ·
    refine ⟨8843529926455999857943315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47165492941098665909031013 8843529926455999857943315)
    ·
      refine ⟨13265294889683999786914973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8843529926455999857943315 13265294889683999786914973)
      ·
        refine ⟨4974485583631499920093115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13265294889683999786914973 4974485583631499920093115)
        ·
          refine ⟨7461728375447249880139673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4974485583631499920093115 7461728375447249880139673)
          ·
            refine ⟨5596296281585437410104755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7461728375447249880139673 5596296281585437410104755)
            ·
              refine ⟨8394444422378156115157133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5596296281585437410104755 8394444422378156115157133)
              ·
                refine ⟨3147916658391808543183925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8394444422378156115157133 3147916658391808543183925)
                ·
                  refine ⟨295117186724232050923493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3147916658391808543183925 295117186724232050923493)
                  ·
                    rfl

theorem cell22_2586324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_2586324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2586324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2586324 prefixEnd_2586324 := by exact prefixLift 2586324
  have htrace : WordTrace (prefixWord ++ tailWord_2586324) baseStart_2586324 baseEnd_2586324 := by
    simpa [prefixWord, tailWord_2586324, baseEnd_2586324] using wordTrace_append hprefix tailTrace_2586324
  have hstable : (prefixWord ++ tailWord_2586324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586324).length < 2 ^ (prefixWord ++ tailWord_2586324).sum := by decide
  have hdescent : baseEnd_2586324 < baseStart_2586324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586335 : List Nat := [1, 1, 2, 3, 2, 2, 2, 1, 8]
def baseStart_2586335 : Nat := 118140960795 + 2586335 * 2 ^ 59
def prefixEnd_2586335 : Nat := 4983230072969 + 3 ^ 40 * 2586335 * 2
def baseEnd_2586335 : Nat := 295118441899165263581815

theorem tailTrace_2586335 : CollatzResearch.WordTrace tailWord_2586335 prefixEnd_2586335 295118441899165263581815 := by
  unfold tailWord_2586335
  simp only [CollatzResearch.WordTrace]
  refine ⟨94331387085157480696712459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62887591390104987131141639 94331387085157480696712459)
  ·
    refine ⟨141497080627736221045068689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94331387085157480696712459 141497080627736221045068689)
    ·
      refine ⟨106122810470802165783801517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141497080627736221045068689 106122810470802165783801517)
      ·
        refine ⟨39796053926550812168925569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106122810470802165783801517 39796053926550812168925569)
        ·
          refine ⟨29847040444913109126694177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39796053926550812168925569 29847040444913109126694177)
          ·
            refine ⟨22385280333684831845020633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29847040444913109126694177 22385280333684831845020633)
            ·
              refine ⟨16788960250263623883765475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22385280333684831845020633 16788960250263623883765475)
              ·
                refine ⟨25183440375395435825648213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16788960250263623883765475 25183440375395435825648213)
                ·
                  refine ⟨295118441899165263581815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25183440375395435825648213 295118441899165263581815)
                  ·
                    rfl

theorem cell22_2586335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 8].length) (baseStart_2586335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2586335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2586335 prefixEnd_2586335 := by exact prefixLift 2586335
  have htrace : WordTrace (prefixWord ++ tailWord_2586335) baseStart_2586335 baseEnd_2586335 := by
    simpa [prefixWord, tailWord_2586335, baseEnd_2586335] using wordTrace_append hprefix tailTrace_2586335
  have hstable : (prefixWord ++ tailWord_2586335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586335).length < 2 ^ (prefixWord ++ tailWord_2586335).sum := by decide
  have hdescent : baseEnd_2586335 < baseStart_2586335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586367 : List Nat := [1, 1, 2, 2, 1, 3, 2, 3, 4, 3]
def baseStart_2586367 : Nat := 118140960795 + 2586367 * 2 ^ 59
def prefixEnd_2586367 : Nat := 4983230072969 + 3 ^ 40 * 2586367 * 2
def baseEnd_2586367 : Nat := 885366279951458373945347

theorem tailTrace_2586367 : CollatzResearch.WordTrace tailWord_2586367 prefixEnd_2586367 885366279951458373945347 := by
  unfold tailWord_2586367
  simp only [CollatzResearch.WordTrace]
  refine ⟨94332554221041550161877355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62888369480694366774584903 94332554221041550161877355)
  ·
    refine ⟨141498831331562325242816033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94332554221041550161877355 141498831331562325242816033)
    ·
      refine ⟨106124123498671743932112025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141498831331562325242816033 106124123498671743932112025)
      ·
        refine ⟨79593092624003807949084019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106124123498671743932112025 79593092624003807949084019)
        ·
          refine ⟨119389638936005711923626029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79593092624003807949084019 119389638936005711923626029)
          ·
            refine ⟨44771114601002141971359761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119389638936005711923626029 44771114601002141971359761)
            ·
              refine ⟨33578335950751606478519821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44771114601002141971359761 33578335950751606478519821)
              ·
                refine ⟨12591875981531852429444933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33578335950751606478519821 12591875981531852429444933)
                ·
                  refine ⟨2360976746537222330520925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12591875981531852429444933 2360976746537222330520925)
                  ·
                    refine ⟨885366279951458373945347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2360976746537222330520925 885366279951458373945347)
                    ·
                      rfl

theorem cell22_2586367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 4, 3].length) (baseStart_2586367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2586367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2586367 prefixEnd_2586367 := by exact prefixLift 2586367
  have htrace : WordTrace (prefixWord ++ tailWord_2586367) baseStart_2586367 baseEnd_2586367 := by
    simpa [prefixWord, tailWord_2586367, baseEnd_2586367] using wordTrace_append hprefix tailTrace_2586367
  have hstable : (prefixWord ++ tailWord_2586367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586367).length < 2 ^ (prefixWord ++ tailWord_2586367).sum := by decide
  have hdescent : baseEnd_2586367 < baseStart_2586367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586382 : List Nat := [4, 1, 1, 2, 1, 1, 2, 2, 4, 4]
def baseStart_2586382 : Nat := 118140960795 + 2586382 * 2 ^ 59
def prefixEnd_2586382 : Nat := 4983230072969 + 3 ^ 40 * 2586382 * 2
def baseEnd_2586382 : Nat := 885371414758003334820301

theorem tailTrace_2586382 : CollatzResearch.WordTrace tailWord_2586382 prefixEnd_2586382 885371414758003334820301 := by
  unfold tailWord_2586382
  simp only [CollatzResearch.WordTrace]
  refine ⟨11791637664498400965459175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62888734210658138482448933 11791637664498400965459175)
  ·
    refine ⟨17687456496747601448188763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11791637664498400965459175 17687456496747601448188763)
    ·
      refine ⟨26531184745121402172283145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17687456496747601448188763 26531184745121402172283145)
      ·
        refine ⟨19898388558841051629212359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26531184745121402172283145 19898388558841051629212359)
        ·
          refine ⟨29847582838261577443818539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19898388558841051629212359 29847582838261577443818539)
          ·
            refine ⟨44771374257392366165727809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29847582838261577443818539 44771374257392366165727809)
            ·
              refine ⟨33578530693044274624295857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44771374257392366165727809 33578530693044274624295857)
              ·
                refine ⟨25183898019783205968221893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33578530693044274624295857 25183898019783205968221893)
                ·
                  refine ⟨4721980878709351119041605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25183898019783205968221893 4721980878709351119041605)
                  ·
                    refine ⟨885371414758003334820301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4721980878709351119041605 885371414758003334820301)
                    ·
                      rfl

theorem cell22_2586382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_2586382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2586382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2586382 prefixEnd_2586382 := by exact prefixLift 2586382
  have htrace : WordTrace (prefixWord ++ tailWord_2586382) baseStart_2586382 baseEnd_2586382 := by
    simpa [prefixWord, tailWord_2586382, baseEnd_2586382] using wordTrace_append hprefix tailTrace_2586382
  have hstable : (prefixWord ++ tailWord_2586382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586382).length < 2 ^ (prefixWord ++ tailWord_2586382).sum := by decide
  have hdescent : baseEnd_2586382 < baseStart_2586382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586395 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 2, 7]
def baseStart_2586395 : Nat := 118140960795 + 2586395 * 2 ^ 59
def prefixEnd_2586395 : Nat := 4983230072969 + 3 ^ 40 * 2586395 * 2
def baseEnd_2586395 : Nat := 885375864923675634245261

theorem tailTrace_2586395 : CollatzResearch.WordTrace tailWord_2586395 prefixEnd_2586395 885375864923675634245261 := by
  unfold tailWord_2586395
  simp only [CollatzResearch.WordTrace]
  refine ⟨94333575464940110943896639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62889050309960073962597759 94333575464940110943896639)
  ·
    refine ⟨141500363197410166415844959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94333575464940110943896639 141500363197410166415844959)
    ·
      refine ⟨212250544796115249623767439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141500363197410166415844959 212250544796115249623767439)
      ·
        refine ⟨318375817194172874435651159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212250544796115249623767439 318375817194172874435651159)
        ·
          refine ⟨477563725791259311653476739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318375817194172874435651159 477563725791259311653476739)
          ·
            refine ⟨716345588686888967480215109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 477563725791259311653476739 716345588686888967480215109)
            ·
              refine ⟨134314797878791681402540333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 716345588686888967480215109 134314797878791681402540333)
              ·
                refine ⟨50368049204546880525952625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134314797878791681402540333 50368049204546880525952625)
                ·
                  refine ⟨37776036903410160394464469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50368049204546880525952625 37776036903410160394464469)
                  ·
                    refine ⟨885375864923675634245261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37776036903410160394464469 885375864923675634245261)
                    ·
                      rfl

theorem cell22_2586395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 7].length) (baseStart_2586395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2586395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2586395 prefixEnd_2586395 := by exact prefixLift 2586395
  have htrace : WordTrace (prefixWord ++ tailWord_2586395) baseStart_2586395 baseEnd_2586395 := by
    simpa [prefixWord, tailWord_2586395, baseEnd_2586395] using wordTrace_append hprefix tailTrace_2586395
  have hstable : (prefixWord ++ tailWord_2586395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586395).length < 2 ^ (prefixWord ++ tailWord_2586395).sum := by decide
  have hdescent : baseEnd_2586395 < baseStart_2586395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586414 : List Nat := [4, 1, 3, 2, 2, 1, 9]
def baseStart_2586414 : Nat := 118140960795 + 2586414 * 2 ^ 59
def prefixEnd_2586414 : Nat := 4983230072969 + 3 ^ 40 * 2586414 * 2
def baseEnd_2586414 : Nat := 32791939593035774741489

theorem tailTrace_2586414 : CollatzResearch.WordTrace tailWord_2586414 prefixEnd_2586414 32791939593035774741489 := by
  unfold tailWord_2586414
  simp only [CollatzResearch.WordTrace]
  refine ⟨11791783556483909648604787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62889512301247518125892197 11791783556483909648604787)
  ·
    refine ⟨17687675334725864472907181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11791783556483909648604787 17687675334725864472907181)
    ·
      refine ⟨6632878250522199177340193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17687675334725864472907181 6632878250522199177340193)
      ·
        refine ⟨4974658687891649383005145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6632878250522199177340193 4974658687891649383005145)
        ·
          refine ⟨3730994015918737037253859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4974658687891649383005145 3730994015918737037253859)
          ·
            refine ⟨5596491023878105555880789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3730994015918737037253859 5596491023878105555880789)
            ·
              refine ⟨32791939593035774741489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5596491023878105555880789 32791939593035774741489)
              ·
                rfl

theorem cell22_2586414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 9].length) (baseStart_2586414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2586414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2586414 prefixEnd_2586414 := by exact prefixLift 2586414
  have htrace : WordTrace (prefixWord ++ tailWord_2586414) baseStart_2586414 baseEnd_2586414 := by
    simpa [prefixWord, tailWord_2586414, baseEnd_2586414] using wordTrace_append hprefix tailTrace_2586414
  have hstable : (prefixWord ++ tailWord_2586414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586414).length < 2 ^ (prefixWord ++ tailWord_2586414).sum := by decide
  have hdescent : baseEnd_2586414 < baseStart_2586414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586463 : List Nat := [1, 1, 2, 3, 1, 6, 1, 3, 1, 3]
def baseStart_2586463 : Nat := 118140960795 + 2586463 * 2 ^ 59
def prefixEnd_2586463 : Nat := 4983230072969 + 3 ^ 40 * 2586463 * 2
def baseEnd_2586463 : Nat := 885399142713346123545053

theorem tailTrace_2586463 : CollatzResearch.WordTrace tailWord_2586463 prefixEnd_2586463 885399142713346123545053 := by
  unfold tailWord_2586463
  simp only [CollatzResearch.WordTrace]
  refine ⟨94336055628693758557372043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62890703752462505704914695 94336055628693758557372043)
  ·
    refine ⟨141504083443040637836058065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94336055628693758557372043 141504083443040637836058065)
    ·
      refine ⟨106128062582280478377043549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141504083443040637836058065 106128062582280478377043549)
      ·
        refine ⟨39798023468355179391391331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106128062582280478377043549 39798023468355179391391331)
        ·
          refine ⟨59697035202532769087086997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39798023468355179391391331 59697035202532769087086997)
          ·
            refine ⟨2798298525118723550957203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 59697035202532769087086997 2798298525118723550957203)
            ·
              refine ⟨4197447787678085326435805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2798298525118723550957203 4197447787678085326435805)
              ·
                refine ⟨1574042920379281997413427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4197447787678085326435805 1574042920379281997413427)
                ·
                  refine ⟨2361064380568922996120141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1574042920379281997413427 2361064380568922996120141)
                  ·
                    refine ⟨885399142713346123545053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2361064380568922996120141 885399142713346123545053)
                    ·
                      rfl

theorem cell22_2586463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 3, 1, 3].length) (baseStart_2586463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2586463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2586463 prefixEnd_2586463 := by exact prefixLift 2586463
  have htrace : WordTrace (prefixWord ++ tailWord_2586463) baseStart_2586463 baseEnd_2586463 := by
    simpa [prefixWord, tailWord_2586463, baseEnd_2586463] using wordTrace_append hprefix tailTrace_2586463
  have hstable : (prefixWord ++ tailWord_2586463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586463).length < 2 ^ (prefixWord ++ tailWord_2586463).sum := by decide
  have hdescent : baseEnd_2586463 < baseStart_2586463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586506 : List Nat := [3, 1, 2, 4, 2, 1, 1, 1, 3, 4]
def baseStart_2586506 : Nat := 118140960795 + 2586506 * 2 ^ 59
def prefixEnd_2586506 : Nat := 4983230072969 + 3 ^ 40 * 2586506 * 2
def baseEnd_2586506 : Nat := 885413862492108344719921

theorem tailTrace_2586506 : CollatzResearch.WordTrace tailWord_2586506 prefixEnd_2586506 885413862492108344719921 := by
  unfold tailWord_2586506
  simp only [CollatzResearch.WordTrace]
  refine ⟨23584405991884494225296843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62891749311691984600791581 23584405991884494225296843)
  ·
    refine ⟨35376608987826741337945265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23584405991884494225296843 35376608987826741337945265)
    ·
      refine ⟨26532456740870056003458949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35376608987826741337945265 26532456740870056003458949)
      ·
        refine ⟨4974835638913135500648553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26532456740870056003458949 4974835638913135500648553)
        ·
          refine ⟨3731126729184851625486415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4974835638913135500648553 3731126729184851625486415)
          ·
            refine ⟨5596690093777277438229623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3731126729184851625486415 5596690093777277438229623)
            ·
              refine ⟨8395035140665916157344435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5596690093777277438229623 8395035140665916157344435)
              ·
                refine ⟨12592552710998874236016653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8395035140665916157344435 12592552710998874236016653)
                ·
                  refine ⟨4722207266624577838506245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12592552710998874236016653 4722207266624577838506245)
                  ·
                    refine ⟨885413862492108344719921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4722207266624577838506245 885413862492108344719921)
                    ·
                      rfl

theorem cell22_2586506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_2586506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2586506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2586506 prefixEnd_2586506 := by exact prefixLift 2586506
  have htrace : WordTrace (prefixWord ++ tailWord_2586506) baseStart_2586506 baseEnd_2586506 := by
    simpa [prefixWord, tailWord_2586506, baseEnd_2586506] using wordTrace_append hprefix tailTrace_2586506
  have hstable : (prefixWord ++ tailWord_2586506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586506).length < 2 ^ (prefixWord ++ tailWord_2586506).sum := by decide
  have hdescent : baseEnd_2586506 < baseStart_2586506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586519 : List Nat := [1, 1, 3, 3, 1, 4, 1, 2, 1, 5]
def baseStart_2586519 : Nat := 118140960795 + 2586519 * 2 ^ 59
def prefixEnd_2586519 : Nat := 4983230072969 + 3 ^ 40 * 2586519 * 2
def baseEnd_2586519 : Nat := 885418312657780644144881

theorem tailTrace_2586519 : CollatzResearch.WordTrace tailWord_2586519 prefixEnd_2586519 885418312657780644144881 := by
  unfold tailWord_2586519
  simp only [CollatzResearch.WordTrace]
  refine ⟨94338098116490880121410611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62892065410993920080940407 94338098116490880121410611)
  ·
    refine ⟨141507147174736320182115917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94338098116490880121410611 141507147174736320182115917)
    ·
      refine ⟨53065180190526120068293469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141507147174736320182115917 53065180190526120068293469)
      ·
        refine ⟨19899442571447295025610051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53065180190526120068293469 19899442571447295025610051)
        ·
          refine ⟨29849163857170942538415077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19899442571447295025610051 29849163857170942538415077)
          ·
            refine ⟨5596718223219551725952827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29849163857170942538415077 5596718223219551725952827)
            ·
              refine ⟨8395077334829327588929241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5596718223219551725952827 8395077334829327588929241)
              ·
                refine ⟨6296308001121995691696931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8395077334829327588929241 6296308001121995691696931)
                ·
                  refine ⟨9444462001682993537545397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6296308001121995691696931 9444462001682993537545397)
                  ·
                    refine ⟨885418312657780644144881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9444462001682993537545397 885418312657780644144881)
                    ·
                      rfl

theorem cell22_2586519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 5].length) (baseStart_2586519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2586519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2586519 prefixEnd_2586519 := by exact prefixLift 2586519
  have htrace : WordTrace (prefixWord ++ tailWord_2586519) baseStart_2586519 baseEnd_2586519 := by
    simpa [prefixWord, tailWord_2586519, baseEnd_2586519] using wordTrace_append hprefix tailTrace_2586519
  have hstable : (prefixWord ++ tailWord_2586519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586519).length < 2 ^ (prefixWord ++ tailWord_2586519).sum := by decide
  have hdescent : baseEnd_2586519 < baseStart_2586519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586532 : List Nat := [2, 3, 1, 2, 1, 13]
def baseStart_2586532 : Nat := 118140960795 + 2586532 * 2 ^ 59
def prefixEnd_2586532 : Nat := 4983230072969 + 3 ^ 40 * 2586532 * 2
def baseEnd_2586532 : Nat := 10931145220042628932961

theorem tailTrace_2586532 : CollatzResearch.WordTrace tailWord_2586532 prefixEnd_2586532 10931145220042628932961 := by
  unfold tailWord_2586532
  simp only [CollatzResearch.WordTrace]
  refine ⟨47169286132721891670816925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62892381510295855561089233 47169286132721891670816925)
  ·
    refine ⟨17688482299770709376556347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47169286132721891670816925 17688482299770709376556347)
    ·
      refine ⟨26532723449656064064834521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17688482299770709376556347 26532723449656064064834521)
      ·
        refine ⟨19899542587242048048625891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26532723449656064064834521 19899542587242048048625891)
        ·
          refine ⟨29849313880863072072938837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19899542587242048048625891 29849313880863072072938837)
          ·
            refine ⟨10931145220042628932961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 29849313880863072072938837 10931145220042628932961)
            ·
              rfl

theorem cell22_2586532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 13].length) (baseStart_2586532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2586532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2586532 prefixEnd_2586532 := by exact prefixLift 2586532
  have htrace : WordTrace (prefixWord ++ tailWord_2586532) baseStart_2586532 baseEnd_2586532 := by
    simpa [prefixWord, tailWord_2586532, baseEnd_2586532] using wordTrace_append hprefix tailTrace_2586532
  have hstable : (prefixWord ++ tailWord_2586532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586532).length < 2 ^ (prefixWord ++ tailWord_2586532).sum := by decide
  have hdescent : baseEnd_2586532 < baseStart_2586532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586549 : List Nat := [1, 3, 3, 2, 1, 2, 3, 7]
def baseStart_2586549 : Nat := 118140960795 + 2586549 * 2 ^ 59
def prefixEnd_2586549 : Nat := 4983230072969 + 3 ^ 40 * 2586549 * 2
def baseEnd_2586549 : Nat := 98380953585652285099421

theorem tailTrace_2586549 : CollatzResearch.WordTrace tailWord_2586549 prefixEnd_2586549 98380953585652285099421 := by
  unfold tailWord_2586549
  simp only [CollatzResearch.WordTrace]
  refine ⟨94339192306382195245002701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62892794870921463496668467 94339192306382195245002701)
  ·
    refine ⟨35377197114893323216876013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94339192306382195245002701 35377197114893323216876013)
    ·
      refine ⟨13266448918084996206328505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35377197114893323216876013 13266448918084996206328505)
      ·
        refine ⟨9949836688563747154746379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13266448918084996206328505 9949836688563747154746379)
        ·
          refine ⟨14924755032845620732119569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9949836688563747154746379 14924755032845620732119569)
          ·
            refine ⟨11193566274634215549089677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14924755032845620732119569 11193566274634215549089677)
            ·
              refine ⟨4197587352987830830908629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11193566274634215549089677 4197587352987830830908629)
              ·
                refine ⟨98380953585652285099421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4197587352987830830908629 98380953585652285099421)
                ·
                  rfl

theorem cell22_2586549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 7].length) (baseStart_2586549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2586549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2586549 prefixEnd_2586549 := by exact prefixLift 2586549
  have htrace : WordTrace (prefixWord ++ tailWord_2586549) baseStart_2586549 baseEnd_2586549 := by
    simpa [prefixWord, tailWord_2586549, baseEnd_2586549] using wordTrace_append hprefix tailTrace_2586549
  have hstable : (prefixWord ++ tailWord_2586549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586549).length < 2 ^ (prefixWord ++ tailWord_2586549).sum := by decide
  have hdescent : baseEnd_2586549 < baseStart_2586549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586684 : List Nat := [2, 2, 2, 2, 2, 1, 1, 10]
def baseStart_2586684 : Nat := 118140960795 + 2586684 * 2 ^ 59
def prefixEnd_2586684 : Nat := 4983230072969 + 3 ^ 40 * 2586684 * 2
def baseEnd_2586684 : Nat := 98386088392197245974375

theorem tailTrace_2586684 : CollatzResearch.WordTrace tailWord_2586684 prefixEnd_2586684 98386088392197245974375 := by
  unfold tailWord_2586684
  simp only [CollatzResearch.WordTrace]
  refine ⟨47172058080446556650583553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62896077440595408867444737 47172058080446556650583553)
  ·
    refine ⟨35379043560334917487937665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47172058080446556650583553 35379043560334917487937665)
    ·
      refine ⟨26534282670251188115953249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35379043560334917487937665 26534282670251188115953249)
      ·
        refine ⟨19900712002688391086964937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26534282670251188115953249 19900712002688391086964937)
        ·
          refine ⟨14925534002016293315223703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19900712002688391086964937 14925534002016293315223703)
          ·
            refine ⟨22388301003024439972835555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14925534002016293315223703 22388301003024439972835555)
            ·
              refine ⟨33582451504536659959253333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22388301003024439972835555 33582451504536659959253333)
              ·
                refine ⟨98386088392197245974375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 33582451504536659959253333 98386088392197245974375)
                ·
                  rfl

theorem cell22_2586684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 10].length) (baseStart_2586684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2586684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2586684 prefixEnd_2586684 := by exact prefixLift 2586684
  have htrace : WordTrace (prefixWord ++ tailWord_2586684) baseStart_2586684 baseEnd_2586684 := by
    simpa [prefixWord, tailWord_2586684, baseEnd_2586684] using wordTrace_append hprefix tailTrace_2586684
  have hstable : (prefixWord ++ tailWord_2586684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586684).length < 2 ^ (prefixWord ++ tailWord_2586684).sum := by decide
  have hdescent : baseEnd_2586684 < baseStart_2586684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586714 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 1, 8]
def baseStart_2586714 : Nat := 118140960795 + 2586714 * 2 ^ 59
def prefixEnd_2586714 : Nat := 4983230072969 + 3 ^ 40 * 2586714 * 2
def baseEnd_2586714 : Nat := 885485065142865135519283

theorem tailTrace_2586714 : CollatzResearch.WordTrace tailWord_2586714 prefixEnd_2586714 885485065142865135519283 := by
  unfold tailWord_2586714
  simp only [CollatzResearch.WordTrace]
  refine ⟨23586302587696107106189799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62896806900522952283172797 23586302587696107106189799)
  ·
    refine ⟨35379453881544160659284699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23586302587696107106189799 35379453881544160659284699)
    ·
      refine ⟨53069180822316240988927049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35379453881544160659284699 53069180822316240988927049)
      ·
        refine ⟨39801885616737180741695287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53069180822316240988927049 39801885616737180741695287)
        ·
          refine ⟨59702828425105771112542931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39801885616737180741695287 59702828425105771112542931)
          ·
            refine ⟨89554242637658656668814397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59702828425105771112542931 89554242637658656668814397)
            ·
              refine ⟨33582840989121996250805399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89554242637658656668814397 33582840989121996250805399)
              ·
                refine ⟨50374261483682994376208099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33582840989121996250805399 50374261483682994376208099)
                ·
                  refine ⟨75561392225524491564312149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50374261483682994376208099 75561392225524491564312149)
                  ·
                    refine ⟨885485065142865135519283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 75561392225524491564312149 885485065142865135519283)
                    ·
                      rfl

theorem cell22_2586714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_2586714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2586714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2586714 prefixEnd_2586714 := by exact prefixLift 2586714
  have htrace : WordTrace (prefixWord ++ tailWord_2586714) baseStart_2586714 baseEnd_2586714 := by
    simpa [prefixWord, tailWord_2586714, baseEnd_2586714] using wordTrace_append hprefix tailTrace_2586714
  have hstable : (prefixWord ++ tailWord_2586714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586714).length < 2 ^ (prefixWord ++ tailWord_2586714).sum := by decide
  have hdescent : baseEnd_2586714 < baseStart_2586714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586733 : List Nat := [1, 5, 1, 1, 2, 1, 3, 2, 3, 3]
def baseStart_2586733 : Nat := 118140960795 + 2586733 * 2 ^ 59
def prefixEnd_2586733 : Nat := 4983230072969 + 3 ^ 40 * 2586733 * 2
def baseEnd_2586733 : Nat := 885491569231155419294225

theorem tailTrace_2586733 : CollatzResearch.WordTrace tailWord_2586733 prefixEnd_2586733 885491569231155419294225 := by
  unfold tailWord_2586733
  simp only [CollatzResearch.WordTrace]
  refine ⟨94345903337715594669700853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62897268891810396446467235 94345903337715594669700853)
  ·
    refine ⟨8844928437910837000284455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94345903337715594669700853 8844928437910837000284455)
    ·
      refine ⟨13267392656866255500426683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8844928437910837000284455 13267392656866255500426683)
      ·
        refine ⟨19901088985299383250640025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13267392656866255500426683 19901088985299383250640025)
        ·
          refine ⟨14925816738974537437980019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19901088985299383250640025 14925816738974537437980019)
          ·
            refine ⟨22388725108461806156970029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14925816738974537437980019 22388725108461806156970029)
            ·
              refine ⟨8395771915673177308863761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22388725108461806156970029 8395771915673177308863761)
              ·
                refine ⟨6296828936754882981647821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8395771915673177308863761 6296828936754882981647821)
                ·
                  refine ⟨2361310851283081118117933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6296828936754882981647821 2361310851283081118117933)
                  ·
                    refine ⟨885491569231155419294225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2361310851283081118117933 885491569231155419294225)
                    ·
                      rfl

theorem cell22_2586733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_2586733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2586733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2586733 prefixEnd_2586733 := by exact prefixLift 2586733
  have htrace : WordTrace (prefixWord ++ tailWord_2586733) baseStart_2586733 baseEnd_2586733 := by
    simpa [prefixWord, tailWord_2586733, baseEnd_2586733] using wordTrace_append hprefix tailTrace_2586733
  have hstable : (prefixWord ++ tailWord_2586733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586733).length < 2 ^ (prefixWord ++ tailWord_2586733).sum := by decide
  have hdescent : baseEnd_2586733 < baseStart_2586733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586744 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 3, 7]
def baseStart_2586744 : Nat := 118140960795 + 2586744 * 2 ^ 59
def prefixEnd_2586744 : Nat := 4983230072969 + 3 ^ 40 * 2586744 * 2
def baseEnd_2586744 : Nat := 885495334755955057269191

theorem tailTrace_2586744 : CollatzResearch.WordTrace tailWord_2586744 prefixEnd_2586744 885495334755955057269191 := by
  unfold tailWord_2586744
  simp only [CollatzResearch.WordTrace]
  refine ⟨47173152270337871774175643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62897536360450495698900857 47173152270337871774175643)
  ·
    refine ⟨70759728405506807661263465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47173152270337871774175643 70759728405506807661263465)
    ·
      refine ⟨53069796304130105745947599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70759728405506807661263465 53069796304130105745947599)
      ·
        refine ⟨79604694456195158618921399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53069796304130105745947599 79604694456195158618921399)
        ·
          refine ⟨119407041684292737928382099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79604694456195158618921399 119407041684292737928382099)
          ·
            refine ⟨179110562526439106892573149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119407041684292737928382099 179110562526439106892573149)
            ·
              refine ⟨67166460947414665084714931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 179110562526439106892573149 67166460947414665084714931)
              ·
                refine ⟨100749691421121997627072397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67166460947414665084714931 100749691421121997627072397)
                ·
                  refine ⟨37781134282920749110152149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100749691421121997627072397 37781134282920749110152149)
                  ·
                    refine ⟨885495334755955057269191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37781134282920749110152149 885495334755955057269191)
                    ·
                      rfl

theorem cell22_2586744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_2586744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2586744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2586744 prefixEnd_2586744 := by exact prefixLift 2586744
  have htrace : WordTrace (prefixWord ++ tailWord_2586744) baseStart_2586744 baseEnd_2586744 := by
    simpa [prefixWord, tailWord_2586744, baseEnd_2586744] using wordTrace_append hprefix tailTrace_2586744
  have hstable : (prefixWord ++ tailWord_2586744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586744).length < 2 ^ (prefixWord ++ tailWord_2586744).sum := by decide
  have hdescent : baseEnd_2586744 < baseStart_2586744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586821 : List Nat := [1, 3, 1, 1, 1, 1, 5, 1, 4, 4]
def baseStart_2586821 : Nat := 118140960795 + 2586821 * 2 ^ 59
def prefixEnd_2586821 : Nat := 4983230072969 + 3 ^ 40 * 2586821 * 2
def baseEnd_2586821 : Nat := 885521693429552523093955

theorem tailTrace_2586821 : CollatzResearch.WordTrace tailWord_2586821 prefixEnd_2586821 885521693429552523093955 := by
  unfold tailWord_2586821
  simp only [CollatzResearch.WordTrace]
  refine ⟨94349112961396785698904317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62899408640931190465936211 94349112961396785698904317)
  ·
    refine ⟨35380917360523794637089119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94349112961396785698904317 35380917360523794637089119)
    ·
      refine ⟨53071376040785691955633679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35380917360523794637089119 53071376040785691955633679)
      ·
        refine ⟨79607064061178537933450519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53071376040785691955633679 79607064061178537933450519)
        ·
          refine ⟨119410596091767806900175779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79607064061178537933450519 119410596091767806900175779)
          ·
            refine ⟨179115894137651710350263669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119410596091767806900175779 179115894137651710350263669)
            ·
              refine ⟨16792115075404847845337219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 179115894137651710350263669 16792115075404847845337219)
              ·
                refine ⟨25188172613107271768005829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16792115075404847845337219 25188172613107271768005829)
                ·
                  refine ⟨4722782364957613456501093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25188172613107271768005829 4722782364957613456501093)
                  ·
                    refine ⟨885521693429552523093955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4722782364957613456501093 885521693429552523093955)
                    ·
                      rfl

theorem cell22_2586821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 4, 4].length) (baseStart_2586821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2586821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2586821 prefixEnd_2586821 := by exact prefixLift 2586821
  have htrace : WordTrace (prefixWord ++ tailWord_2586821) baseStart_2586821 baseEnd_2586821 := by
    simpa [prefixWord, tailWord_2586821, baseEnd_2586821] using wordTrace_append hprefix tailTrace_2586821
  have hstable : (prefixWord ++ tailWord_2586821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586821).length < 2 ^ (prefixWord ++ tailWord_2586821).sum := by decide
  have hdescent : baseEnd_2586821 < baseStart_2586821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586840 : List Nat := [2, 1, 2, 2, 4, 2, 1, 3, 2, 3]
def baseStart_2586840 : Nat := 118140960795 + 2586840 * 2 ^ 59
def prefixEnd_2586840 : Nat := 4983230072969 + 3 ^ 40 * 2586840 * 2
def baseEnd_2586840 : Nat := 885528197517842806868897

theorem tailTrace_2586840 : CollatzResearch.WordTrace tailWord_2586840 prefixEnd_2586840 885528197517842806868897 := by
  unfold tailWord_2586840
  simp only [CollatzResearch.WordTrace]
  refine ⟨47174902974163975971922987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62899870632218634629230649 47174902974163975971922987)
  ·
    refine ⟨70762354461245963957884481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47174902974163975971922987 70762354461245963957884481)
    ·
      refine ⟨53071765845934472968413361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70762354461245963957884481 53071765845934472968413361)
      ·
        refine ⟨39803824384450854726310021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53071765845934472968413361 39803824384450854726310021)
        ·
          refine ⟨7463217072084535261183129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39803824384450854726310021 7463217072084535261183129)
          ·
            refine ⟨5597412804063401445887347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7463217072084535261183129 5597412804063401445887347)
            ·
              refine ⟨8396119206095102168831021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5597412804063401445887347 8396119206095102168831021)
              ·
                refine ⟨3148544702285663313311633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8396119206095102168831021 3148544702285663313311633)
                ·
                  refine ⟨2361408526714247484983725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3148544702285663313311633 2361408526714247484983725)
                  ·
                    refine ⟨885528197517842806868897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2361408526714247484983725 885528197517842806868897)
                    ·
                      rfl

theorem cell22_2586840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 3, 2, 3].length) (baseStart_2586840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2586840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2586840 prefixEnd_2586840 := by exact prefixLift 2586840
  have htrace : WordTrace (prefixWord ++ tailWord_2586840) baseStart_2586840 baseEnd_2586840 := by
    simpa [prefixWord, tailWord_2586840, baseEnd_2586840] using wordTrace_append hprefix tailTrace_2586840
  have hstable : (prefixWord ++ tailWord_2586840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586840).length < 2 ^ (prefixWord ++ tailWord_2586840).sum := by decide
  have hdescent : baseEnd_2586840 < baseStart_2586840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586844 : List Nat := [2, 2, 5, 2, 1, 2, 1, 2, 1, 4]
def baseStart_2586844 : Nat := 118140960795 + 2586844 * 2 ^ 59
def prefixEnd_2586844 : Nat := 4983230072969 + 3 ^ 40 * 2586844 * 2
def baseEnd_2586844 : Nat := 885529566799588129768885

theorem tailTrace_2586844 : CollatzResearch.WordTrace tailWord_2586844 prefixEnd_2586844 885529566799588129768885 := by
  unfold tailWord_2586844
  simp only [CollatzResearch.WordTrace]
  refine ⟨47174975920156730313495793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62899967893542307084661057 47174975920156730313495793)
  ·
    refine ⟨35381231940117547735121845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47174975920156730313495793 35381231940117547735121845)
    ·
      refine ⟨3316990494386020100167673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35381231940117547735121845 3316990494386020100167673)
      ·
        refine ⟨2487742870789515075125755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3316990494386020100167673 2487742870789515075125755)
        ·
          refine ⟨3731614306184272612688633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2487742870789515075125755 3731614306184272612688633)
          ·
            refine ⟨2798710729638204459516475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3731614306184272612688633 2798710729638204459516475)
            ·
              refine ⟨4198066094457306689274713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2798710729638204459516475 4198066094457306689274713)
              ·
                refine ⟨3148549570842980016956035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4198066094457306689274713 3148549570842980016956035)
                ·
                  refine ⟨4722824356264470025434053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3148549570842980016956035 4722824356264470025434053)
                  ·
                    refine ⟨885529566799588129768885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4722824356264470025434053 885529566799588129768885)
                    ·
                      rfl

theorem cell22_2586844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_2586844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2586844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2586844 prefixEnd_2586844 := by exact prefixLift 2586844
  have htrace : WordTrace (prefixWord ++ tailWord_2586844) baseStart_2586844 baseEnd_2586844 := by
    simpa [prefixWord, tailWord_2586844, baseEnd_2586844] using wordTrace_append hprefix tailTrace_2586844
  have hstable : (prefixWord ++ tailWord_2586844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586844).length < 2 ^ (prefixWord ++ tailWord_2586844).sum := by decide
  have hdescent : baseEnd_2586844 < baseStart_2586844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586855 : List Nat := [1, 1, 5, 3, 1, 2, 2, 1, 2, 4]
def baseStart_2586855 : Nat := 118140960795 + 2586855 * 2 ^ 59
def prefixEnd_2586855 : Nat := 4983230072969 + 3 ^ 40 * 2586855 * 2
def baseEnd_2586855 : Nat := 885533332324387767743851

theorem tailTrace_2586855 : CollatzResearch.WordTrace tailWord_2586855 prefixEnd_2586855 885533332324387767743851 := by
  unfold tailWord_2586855
  simp only [CollatzResearch.WordTrace]
  refine ⟨94350353043273609505642019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62900235362182406337094679 94350353043273609505642019)
  ·
    refine ⟨141525529564910414258463029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94350353043273609505642019 141525529564910414258463029)
    ·
      refine ⟨13268018396710351336730909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 141525529564910414258463029 13268018396710351336730909)
      ·
        refine ⟨4975506898766381751274091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13268018396710351336730909 4975506898766381751274091)
        ·
          refine ⟨7463260348149572626911137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4975506898766381751274091 7463260348149572626911137)
          ·
            refine ⟨5597445261112179470183353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7463260348149572626911137 5597445261112179470183353)
            ·
              refine ⟨4198083945834134602637515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5597445261112179470183353 4198083945834134602637515)
              ·
                refine ⟨6297125918751201903956273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4198083945834134602637515 6297125918751201903956273)
                ·
                  refine ⟨4722844439063401427967205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6297125918751201903956273 4722844439063401427967205)
                  ·
                    refine ⟨885533332324387767743851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4722844439063401427967205 885533332324387767743851)
                    ·
                      rfl

theorem cell22_2586855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_2586855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2586855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2586855 prefixEnd_2586855 := by exact prefixLift 2586855
  have htrace : WordTrace (prefixWord ++ tailWord_2586855) baseStart_2586855 baseEnd_2586855 := by
    simpa [prefixWord, tailWord_2586855, baseEnd_2586855] using wordTrace_append hprefix tailTrace_2586855
  have hstable : (prefixWord ++ tailWord_2586855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586855).length < 2 ^ (prefixWord ++ tailWord_2586855).sum := by decide
  have hdescent : baseEnd_2586855 < baseStart_2586855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586887 : List Nat := [1, 1, 4, 5, 2, 1, 1, 7]
def baseStart_2586887 : Nat := 118140960795 + 2586887 * 2 ^ 59
def prefixEnd_2586887 : Nat := 4983230072969 + 3 ^ 40 * 2586887 * 2
def baseEnd_2586887 : Nat := 98393809619816705660417

theorem tailTrace_2586887 : CollatzResearch.WordTrace tailWord_2586887 prefixEnd_2586887 98393809619816705660417 := by
  unfold tailWord_2586887
  simp only [CollatzResearch.WordTrace]
  refine ⟨94351520179157678970806915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62901013452771785980537943 94351520179157678970806915)
  ·
    refine ⟨141527280268736518456210373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94351520179157678970806915 141527280268736518456210373)
    ·
      refine ⟨26536365050388097210539445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141527280268736518456210373 26536365050388097210539445)
      ·
        refine ⟨2487784223473884113488073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26536365050388097210539445 2487784223473884113488073)
        ·
          refine ⟨1865838167605413085116055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2487784223473884113488073 1865838167605413085116055)
          ·
            refine ⟨2798757251408119627674083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1865838167605413085116055 2798757251408119627674083)
            ·
              refine ⟨4198135877112179441511125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2798757251408119627674083 4198135877112179441511125)
              ·
                refine ⟨98393809619816705660417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4198135877112179441511125 98393809619816705660417)
                ·
                  rfl

theorem cell22_2586887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 7].length) (baseStart_2586887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2586887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2586887 prefixEnd_2586887 := by exact prefixLift 2586887
  have htrace : WordTrace (prefixWord ++ tailWord_2586887) baseStart_2586887 baseEnd_2586887 := by
    simpa [prefixWord, tailWord_2586887, baseEnd_2586887] using wordTrace_append hprefix tailTrace_2586887
  have hstable : (prefixWord ++ tailWord_2586887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586887).length < 2 ^ (prefixWord ++ tailWord_2586887).sum := by decide
  have hdescent : baseEnd_2586887 < baseStart_2586887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586932 : List Nat := [2, 5, 1, 1, 1, 4, 1, 2, 5]
def baseStart_2586932 : Nat := 118140960795 + 2586932 * 2 ^ 59
def prefixEnd_2586932 : Nat := 4983230072969 + 3 ^ 40 * 2586932 * 2
def baseEnd_2586932 : Nat := 295186563665995077856205

theorem tailTrace_2586932 : CollatzResearch.WordTrace tailWord_2586932 prefixEnd_2586932 295186563665995077856205 := by
  unfold tailWord_2586932
  simp only [CollatzResearch.WordTrace]
  refine ⟨47176580731997325828097525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62902107642663101104130033 47176580731997325828097525)
  ·
    refine ⟨4422804443624749296384143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47176580731997325828097525 4422804443624749296384143)
    ·
      refine ⟨6634206665437123944576215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4422804443624749296384143 6634206665437123944576215)
      ·
        refine ⟨9951309998155685916864323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6634206665437123944576215 9951309998155685916864323)
        ·
          refine ⟨14926964997233528875296485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9951309998155685916864323 14926964997233528875296485)
          ·
            refine ⟨2798805936981286664118091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14926964997233528875296485 2798805936981286664118091)
            ·
              refine ⟨4198208905471929996177137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2798805936981286664118091 4198208905471929996177137)
              ·
                refine ⟨3148656679103947497132853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4198208905471929996177137 3148656679103947497132853)
                ·
                  refine ⟨295186563665995077856205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3148656679103947497132853 295186563665995077856205)
                  ·
                    rfl

theorem cell22_2586932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_2586932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2586932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2586932 prefixEnd_2586932 := by exact prefixLift 2586932
  have htrace : WordTrace (prefixWord ++ tailWord_2586932) baseStart_2586932 baseEnd_2586932 := by
    simpa [prefixWord, tailWord_2586932, baseEnd_2586932] using wordTrace_append hprefix tailTrace_2586932
  have hstable : (prefixWord ++ tailWord_2586932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586932).length < 2 ^ (prefixWord ++ tailWord_2586932).sum := by decide
  have hdescent : baseEnd_2586932 < baseStart_2586932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586943 : List Nat := [1, 1, 2, 2, 4, 1, 4, 1, 6]
def baseStart_2586943 : Nat := 118140960795 + 2586943 * 2 ^ 59
def prefixEnd_2586943 : Nat := 4983230072969 + 3 ^ 40 * 2586943 * 2
def baseEnd_2586943 : Nat := 295187818840928290514527

theorem tailTrace_2586943 : CollatzResearch.WordTrace tailWord_2586943 prefixEnd_2586943 295187818840928290514527 := by
  unfold tailWord_2586943
  simp only [CollatzResearch.WordTrace]
  refine ⟨94353562666954800534845483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62902375111303200356563655 94353562666954800534845483)
  ·
    refine ⟨141530344000432200802268225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94353562666954800534845483 141530344000432200802268225)
    ·
      refine ⟨106147758000324150601701169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141530344000432200802268225 106147758000324150601701169)
      ·
        refine ⟨79610818500243112951275877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106147758000324150601701169 79610818500243112951275877)
        ·
          refine ⟨14927028468795583678364227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79610818500243112951275877 14927028468795583678364227)
          ·
            refine ⟨22390542703193375517546341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14927028468795583678364227 22390542703193375517546341)
            ·
              refine ⟨4198226756848757909539939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22390542703193375517546341 4198226756848757909539939)
              ·
                refine ⟨6297340135273136864309909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4198226756848757909539939 6297340135273136864309909)
                ·
                  refine ⟨295187818840928290514527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6297340135273136864309909 295187818840928290514527)
                  ·
                    rfl

theorem cell22_2586943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 6].length) (baseStart_2586943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2586943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2586943 prefixEnd_2586943 := by exact prefixLift 2586943
  have htrace : WordTrace (prefixWord ++ tailWord_2586943) baseStart_2586943 baseEnd_2586943 := by
    simpa [prefixWord, tailWord_2586943, baseEnd_2586943] using wordTrace_append hprefix tailTrace_2586943
  have hstable : (prefixWord ++ tailWord_2586943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586943).length < 2 ^ (prefixWord ++ tailWord_2586943).sum := by decide
  have hdescent : baseEnd_2586943 < baseStart_2586943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586958 : List Nat := [4, 1, 1, 1, 1, 1, 2, 5, 1, 5]
def baseStart_2586958 : Nat := 118140960795 + 2586958 * 2 ^ 59
def prefixEnd_2586958 : Nat := 4983230072969 + 3 ^ 40 * 2586958 * 2
def baseEnd_2586958 : Nat := 885568591329329832418535

theorem tailTrace_2586958 : CollatzResearch.WordTrace tailWord_2586958 prefixEnd_2586958 885568591329329832418535 := by
  unfold tailWord_2586958
  simp only [CollatzResearch.WordTrace]
  refine ⟨11794263720237557262080191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62902739841266972064427685 11794263720237557262080191)
  ·
    refine ⟨17691395580356335893120287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11794263720237557262080191 17691395580356335893120287)
    ·
      refine ⟨26537093370534503839680431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17691395580356335893120287 26537093370534503839680431)
      ·
        refine ⟨39805640055801755759520647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26537093370534503839680431 39805640055801755759520647)
        ·
          refine ⟨59708460083702633639280971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39805640055801755759520647 59708460083702633639280971)
          ·
            refine ⟨89562690125553950458921457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59708460083702633639280971 89562690125553950458921457)
            ·
              refine ⟨67172017594165462844191093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89562690125553950458921457 67172017594165462844191093)
              ·
                refine ⟨6297376649453012141642915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67172017594165462844191093 6297376649453012141642915)
                ·
                  refine ⟨9446064974179518212464373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6297376649453012141642915 9446064974179518212464373)
                  ·
                    refine ⟨885568591329329832418535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9446064974179518212464373 885568591329329832418535)
                    ·
                      rfl

theorem cell22_2586958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_2586958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2586958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2586958 prefixEnd_2586958 := by exact prefixLift 2586958
  have htrace : WordTrace (prefixWord ++ tailWord_2586958) baseStart_2586958 baseEnd_2586958 := by
    simpa [prefixWord, tailWord_2586958, baseEnd_2586958] using wordTrace_append hprefix tailTrace_2586958
  have hstable : (prefixWord ++ tailWord_2586958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586958).length < 2 ^ (prefixWord ++ tailWord_2586958).sum := by decide
  have hdescent : baseEnd_2586958 < baseStart_2586958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587009 : List Nat := [1, 2, 4, 3, 1, 1, 4, 1, 2, 3]
def baseStart_2587009 : Nat := 118140960795 + 2587009 * 2 ^ 59
def prefixEnd_2587009 : Nat := 4983230072969 + 3 ^ 40 * 2587009 * 2
def baseEnd_2587009 : Nat := 885586049671582699393379

theorem tailTrace_2587009 : CollatzResearch.WordTrace tailWord_2587009 prefixEnd_2587009 885586049671582699393379 := by
  unfold tailWord_2587009
  simp only [CollatzResearch.WordTrace]
  refine ⟨94355969884715693806748081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62903979923143795871165387 94355969884715693806748081)
  ·
    refine ⟨70766977413536770355061061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94355969884715693806748081 70766977413536770355061061)
    ·
      refine ⟨13268808265038144441573949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70766977413536770355061061 13268808265038144441573949)
      ·
        refine ⟨4975803099389304165590231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13268808265038144441573949 4975803099389304165590231)
        ·
          refine ⟨7463704649083956248385347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4975803099389304165590231 7463704649083956248385347)
          ·
            refine ⟨11195556973625934372578021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7463704649083956248385347 11195556973625934372578021)
            ·
              refine ⟨2099166932554862694858379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11195556973625934372578021 2099166932554862694858379)
              ·
                refine ⟨3148750398832294042287569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2099166932554862694858379 3148750398832294042287569)
                ·
                  refine ⟨2361562799124220531715677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3148750398832294042287569 2361562799124220531715677)
                  ·
                    refine ⟨885586049671582699393379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2361562799124220531715677 885586049671582699393379)
                    ·
                      rfl

theorem cell22_2587009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_2587009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2587009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2587009 prefixEnd_2587009 := by exact prefixLift 2587009
  have htrace : WordTrace (prefixWord ++ tailWord_2587009) baseStart_2587009 baseEnd_2587009 := by
    simpa [prefixWord, tailWord_2587009, baseEnd_2587009] using wordTrace_append hprefix tailTrace_2587009
  have hstable : (prefixWord ++ tailWord_2587009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587009).length < 2 ^ (prefixWord ++ tailWord_2587009).sum := by decide
  have hdescent : baseEnd_2587009 < baseStart_2587009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587065 : List Nat := [1, 2, 1, 4, 3, 2, 1, 1, 2, 5]
def baseStart_2587065 : Nat := 118140960795 + 2587065 * 2 ^ 59
def prefixEnd_2587065 : Nat := 4983230072969 + 3 ^ 40 * 2587065 * 2
def baseEnd_2587065 : Nat := 885605219616017219993207

theorem tailTrace_2587065 : CollatzResearch.WordTrace tailWord_2587065 prefixEnd_2587065 885605219616017219993207 := by
  unfold tailWord_2587065
  simp only [CollatzResearch.WordTrace]
  refine ⟨94358012372512815370786649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62905341581675210247191099 94358012372512815370786649)
  ·
    refine ⟨70768509279384611528089987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94358012372512815370786649 70768509279384611528089987)
    ·
      refine ⟨106152763919076917292134981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70768509279384611528089987 106152763919076917292134981)
      ·
        refine ⟨19903643234826921992275309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106152763919076917292134981 19903643234826921992275309)
        ·
          refine ⟨7463866213060095747103241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19903643234826921992275309 7463866213060095747103241)
          ·
            refine ⟨5597899659795071810327431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7463866213060095747103241 5597899659795071810327431)
            ·
              refine ⟨8396849489692607715491147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5597899659795071810327431 8396849489692607715491147)
              ·
                refine ⟨12595274234538911573236721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8396849489692607715491147 12595274234538911573236721)
                ·
                  refine ⟨9446455675904183679927541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12595274234538911573236721 9446455675904183679927541)
                  ·
                    refine ⟨885605219616017219993207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9446455675904183679927541 885605219616017219993207)
                    ·
                      rfl

theorem cell22_2587065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 5].length) (baseStart_2587065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2587065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2587065 prefixEnd_2587065 := by exact prefixLift 2587065
  have htrace : WordTrace (prefixWord ++ tailWord_2587065) baseStart_2587065 baseEnd_2587065 := by
    simpa [prefixWord, tailWord_2587065, baseEnd_2587065] using wordTrace_append hprefix tailTrace_2587065
  have hstable : (prefixWord ++ tailWord_2587065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587065).length < 2 ^ (prefixWord ++ tailWord_2587065).sum := by decide
  have hdescent : baseEnd_2587065 < baseStart_2587065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587080 : List Nat := [2, 1, 3, 1, 3, 2, 2, 1, 3, 4]
def baseStart_2587080 : Nat := 118140960795 + 2587080 * 2 ^ 59
def prefixEnd_2587080 : Nat := 4983230072969 + 3 ^ 40 * 2587080 * 2
def baseEnd_2587080 : Nat := 885610354422562180868161

theorem tailTrace_2587080 : CollatzResearch.WordTrace tailWord_2587080 prefixEnd_2587080 885610354422562180868161 := by
  unfold tailWord_2587080
  simp only [CollatzResearch.WordTrace]
  refine ⟨47179279733729236466291347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62905706311638981955055129 47179279733729236466291347)
  ·
    refine ⟨70768919600593854699437021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47179279733729236466291347 70768919600593854699437021)
    ·
      refine ⟨26538344850222695512288883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70768919600593854699437021 26538344850222695512288883)
      ·
        refine ⟨39807517275334043268433325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26538344850222695512288883 39807517275334043268433325)
        ·
          refine ⟨14927818978250266225662497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39807517275334043268433325 14927818978250266225662497)
          ·
            refine ⟨11195864233687699669246873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14927818978250266225662497 11195864233687699669246873)
            ·
              refine ⟨8396898175265774751935155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11195864233687699669246873 8396898175265774751935155)
              ·
                refine ⟨12595347262898662127902733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8396898175265774751935155 12595347262898662127902733)
                ·
                  refine ⟨4723255223586998297963525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12595347262898662127902733 4723255223586998297963525)
                  ·
                    refine ⟨885610354422562180868161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4723255223586998297963525 885610354422562180868161)
                    ·
                      rfl

theorem cell22_2587080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_2587080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2587080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2587080 prefixEnd_2587080 := by exact prefixLift 2587080
  have htrace : WordTrace (prefixWord ++ tailWord_2587080) baseStart_2587080 baseEnd_2587080 := by
    simpa [prefixWord, tailWord_2587080, baseEnd_2587080] using wordTrace_append hprefix tailTrace_2587080
  have hstable : (prefixWord ++ tailWord_2587080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587080).length < 2 ^ (prefixWord ++ tailWord_2587080).sum := by decide
  have hdescent : baseEnd_2587080 < baseStart_2587080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587112 : List Nat := [2, 1, 4, 1, 1, 3, 2, 4, 4]
def baseStart_2587112 : Nat := 118140960795 + 2587112 * 2 ^ 59
def prefixEnd_2587112 : Nat := 4983230072969 + 3 ^ 40 * 2587112 * 2
def baseEnd_2587112 : Nat := 295207102892174921356021

theorem tailTrace_2587112 : CollatzResearch.WordTrace tailWord_2587112 prefixEnd_2587112 295207102892174921356021 := by
  unfold tailWord_2587112
  simp only [CollatzResearch.WordTrace]
  refine ⟨47179863301671271198873795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62906484402228361598498393 47179863301671271198873795)
  ·
    refine ⟨70769794952506906798310693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47179863301671271198873795 70769794952506906798310693)
    ·
      refine ⟨13269336553595045024683255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70769794952506906798310693 13269336553595045024683255)
      ·
        refine ⟨19904004830392567537024883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13269336553595045024683255 19904004830392567537024883)
        ·
          refine ⟨29856007245588851305537325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19904004830392567537024883 29856007245588851305537325)
          ·
            refine ⟨11196002717095819239576497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29856007245588851305537325 11196002717095819239576497)
            ·
              refine ⟨8397002037821864429682373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11196002717095819239576497 8397002037821864429682373)
              ·
                refine ⟨1574437882091599580565445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8397002037821864429682373 1574437882091599580565445)
                ·
                  refine ⟨295207102892174921356021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1574437882091599580565445 295207102892174921356021)
                  ·
                    rfl

theorem cell22_2587112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 4, 4].length) (baseStart_2587112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2587112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2587112 prefixEnd_2587112 := by exact prefixLift 2587112
  have htrace : WordTrace (prefixWord ++ tailWord_2587112) baseStart_2587112 baseEnd_2587112 := by
    simpa [prefixWord, tailWord_2587112, baseEnd_2587112] using wordTrace_append hprefix tailTrace_2587112
  have hstable : (prefixWord ++ tailWord_2587112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587112).length < 2 ^ (prefixWord ++ tailWord_2587112).sum := by decide
  have hdescent : baseEnd_2587112 < baseStart_2587112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587123 : List Nat := [1, 1, 1, 2, 2, 2, 4, 9]
def baseStart_2587123 : Nat := 118140960795 + 2587123 * 2 ^ 59
def prefixEnd_2587123 : Nat := 4983230072969 + 3 ^ 40 * 2587123 * 2
def baseEnd_2587123 : Nat := 98402786022369378004781

theorem tailTrace_2587123 : CollatzResearch.WordTrace tailWord_2587123 prefixEnd_2587123 98402786022369378004781 := by
  unfold tailWord_2587123
  simp only [CollatzResearch.WordTrace]
  refine ⟨94360127806302691276398023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62906751870868460850932015 94360127806302691276398023)
  ·
    refine ⟨141540191709454036914597035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94360127806302691276398023 141540191709454036914597035)
    ·
      refine ⟨212310287564181055371895553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141540191709454036914597035 212310287564181055371895553)
      ·
        refine ⟨159232715673135791528921665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212310287564181055371895553 159232715673135791528921665)
        ·
          refine ⟨119424536754851843646691249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159232715673135791528921665 119424536754851843646691249)
          ·
            refine ⟨89568402566138882735018437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119424536754851843646691249 89568402566138882735018437)
            ·
              refine ⟨16794075481151040512815957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89568402566138882735018437 16794075481151040512815957)
              ·
                refine ⟨98402786022369378004781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16794075481151040512815957 98402786022369378004781)
                ·
                  rfl

theorem cell22_2587123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 9].length) (baseStart_2587123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2587123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2587123 prefixEnd_2587123 := by exact prefixLift 2587123
  have htrace : WordTrace (prefixWord ++ tailWord_2587123) baseStart_2587123 baseEnd_2587123 := by
    simpa [prefixWord, tailWord_2587123, baseEnd_2587123] using wordTrace_append hprefix tailTrace_2587123
  have hstable : (prefixWord ++ tailWord_2587123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587123).length < 2 ^ (prefixWord ++ tailWord_2587123).sum := by decide
  have hdescent : baseEnd_2587123 < baseStart_2587123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587159 : List Nat := [1, 1, 3, 6, 1, 1, 1, 2, 2, 4]
def baseStart_2587159 : Nat := 118140960795 + 2587159 * 2 ^ 59
def prefixEnd_2587159 : Nat := 4983230072969 + 3 ^ 40 * 2587159 * 2
def baseEnd_2587159 : Nat := 885637397737032308142919

theorem tailTrace_2587159 : CollatzResearch.WordTrace tailWord_2587159 prefixEnd_2587159 885637397737032308142919 := by
  unfold tailWord_2587159
  simp only [CollatzResearch.WordTrace]
  refine ⟨94361440834172269424708531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62907627222781512949805687 94361440834172269424708531)
  ·
    refine ⟨141542161251258404137062797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94361440834172269424708531 141542161251258404137062797)
    ·
      refine ⟨53078310469221901551398549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141542161251258404137062797 53078310469221901551398549)
      ·
        refine ⟨2488045803244776635221807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 53078310469221901551398549 2488045803244776635221807)
        ·
          refine ⟨3732068704867164952832711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2488045803244776635221807 3732068704867164952832711)
          ·
            refine ⟨5598103057300747429249067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3732068704867164952832711 5598103057300747429249067)
            ·
              refine ⟨8397154585951121143873601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5598103057300747429249067 8397154585951121143873601)
              ·
                refine ⟨6297865939463340857905201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8397154585951121143873601 6297865939463340857905201)
                ·
                  refine ⟨4723399454597505643428901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6297865939463340857905201 4723399454597505643428901)
                  ·
                    refine ⟨885637397737032308142919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4723399454597505643428901 885637397737032308142919)
                    ·
                      rfl

theorem cell22_2587159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 2, 4].length) (baseStart_2587159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2587159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2587159 prefixEnd_2587159 := by exact prefixLift 2587159
  have htrace : WordTrace (prefixWord ++ tailWord_2587159) baseStart_2587159 baseEnd_2587159 := by
    simpa [prefixWord, tailWord_2587159, baseEnd_2587159] using wordTrace_append hprefix tailTrace_2587159
  have hstable : (prefixWord ++ tailWord_2587159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587159).length < 2 ^ (prefixWord ++ tailWord_2587159).sum := by decide
  have hdescent : baseEnd_2587159 < baseStart_2587159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587170 : List Nat := [3, 3, 1, 1, 1, 1, 1, 3, 2, 6]
def baseStart_2587170 : Nat := 118140960795 + 2587170 * 2 ^ 59
def prefixEnd_2587170 : Nat := 4983230072969 + 3 ^ 40 * 2587170 * 2
def baseEnd_2587170 : Nat := 885641163261831946117885

theorem tailTrace_2587170 : CollatzResearch.WordTrace tailWord_2587170 prefixEnd_2587170 885641163261831946117885 := by
  unfold tailWord_2587170
  simp only [CollatzResearch.WordTrace]
  refine ⟨23590460509283104575839741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62907894691421612202239309 23590460509283104575839741)
  ·
    refine ⟨8846422690981164215939903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23590460509283104575839741 8846422690981164215939903)
    ·
      refine ⟨13269634036471746323909855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8846422690981164215939903 13269634036471746323909855)
      ·
        refine ⟨19904451054707619485864783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13269634036471746323909855 19904451054707619485864783)
        ·
          refine ⟨29856676582061429228797175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19904451054707619485864783 29856676582061429228797175)
          ·
            refine ⟨44785014873092143843195763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29856676582061429228797175 44785014873092143843195763)
            ·
              refine ⟨67177522309638215764793645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44785014873092143843195763 67177522309638215764793645)
              ·
                refine ⟨25191570866114330911797617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67177522309638215764793645 25191570866114330911797617)
                ·
                  refine ⟨18893678149585748183848213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25191570866114330911797617 18893678149585748183848213)
                  ·
                    refine ⟨885641163261831946117885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18893678149585748183848213 885641163261831946117885)
                    ·
                      rfl

theorem cell22_2587170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_2587170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2587170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2587170 prefixEnd_2587170 := by exact prefixLift 2587170
  have htrace : WordTrace (prefixWord ++ tailWord_2587170) baseStart_2587170 baseEnd_2587170 := by
    simpa [prefixWord, tailWord_2587170, baseEnd_2587170] using wordTrace_append hprefix tailTrace_2587170
  have hstable : (prefixWord ++ tailWord_2587170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587170).length < 2 ^ (prefixWord ++ tailWord_2587170).sum := by decide
  have hdescent : baseEnd_2587170 < baseStart_2587170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587264 : List Nat := [2, 1, 1, 2, 1, 6, 2, 3, 4]
def baseStart_2587264 : Nat := 118140960795 + 2587264 * 2 ^ 59
def prefixEnd_2587264 : Nat := 4983230072969 + 3 ^ 40 * 2587264 * 2
def baseEnd_2587264 : Nat := 295224447127615678089199

theorem tailTrace_2587264 : CollatzResearch.WordTrace tailWord_2587264 prefixEnd_2587264 295224447127615678089199 := by
  unfold tailWord_2587264
  simp only [CollatzResearch.WordTrace]
  refine ⟨47182635249395936178640423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62910180332527914904853897 47182635249395936178640423)
  ·
    refine ⟨70773952874093904267960635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47182635249395936178640423 70773952874093904267960635)
    ·
      refine ⟨106160929311140856401940953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70773952874093904267960635 106160929311140856401940953)
      ·
        refine ⟨79620696983355642301455715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106160929311140856401940953 79620696983355642301455715)
        ·
          refine ⟨119431045475033463452183573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79620696983355642301455715 119431045475033463452183573)
          ·
            refine ⟨5598330256642193599321105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 119431045475033463452183573 5598330256642193599321105)
            ·
              refine ⟨4198747692481645199490829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5598330256642193599321105 4198747692481645199490829)
              ·
                refine ⟨1574530384680616949809061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4198747692481645199490829 1574530384680616949809061)
                ·
                  refine ⟨295224447127615678089199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1574530384680616949809061 295224447127615678089199)
                  ·
                    rfl

theorem cell22_2587264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 3, 4].length) (baseStart_2587264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2587264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2587264 prefixEnd_2587264 := by exact prefixLift 2587264
  have htrace : WordTrace (prefixWord ++ tailWord_2587264) baseStart_2587264 baseEnd_2587264 := by
    simpa [prefixWord, tailWord_2587264, baseEnd_2587264] using wordTrace_append hprefix tailTrace_2587264
  have hstable : (prefixWord ++ tailWord_2587264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587264).length < 2 ^ (prefixWord ++ tailWord_2587264).sum := by decide
  have hdescent : baseEnd_2587264 < baseStart_2587264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587296 : List Nat := [2, 1, 1, 4, 5, 1, 1, 1, 1, 5]
def baseStart_2587296 : Nat := 118140960795 + 2587296 * 2 ^ 59
def prefixEnd_2587296 : Nat := 4983230072969 + 3 ^ 40 * 2587296 * 2
def baseEnd_2587296 : Nat := 885684295636809617467499

theorem tailTrace_2587296 : CollatzResearch.WordTrace tailWord_2587296 prefixEnd_2587296 885684295636809617467499 := by
  unfold tailWord_2587296
  simp only [CollatzResearch.WordTrace]
  refine ⟨47183218817337970911222871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62910958423117294548297161 47183218817337970911222871)
  ·
    refine ⟨70774828226006956366834307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47183218817337970911222871 70774828226006956366834307)
    ·
      refine ⟨106162242339010434550251461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70774828226006956366834307 106162242339010434550251461)
      ·
        refine ⟨19905420438564456478172149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106162242339010434550251461 19905420438564456478172149)
        ·
          refine ⟨1866133166115417794828639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19905420438564456478172149 1866133166115417794828639)
          ·
            refine ⟨2799199749173126692242959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1866133166115417794828639 2799199749173126692242959)
            ·
              refine ⟨4198799623759690038364439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2799199749173126692242959 4198799623759690038364439)
              ·
                refine ⟨6298199435639535057546659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4198799623759690038364439 6298199435639535057546659)
                ·
                  refine ⟨9447299153459302586319989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6298199435639535057546659 9447299153459302586319989)
                  ·
                    refine ⟨885684295636809617467499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9447299153459302586319989 885684295636809617467499)
                    ·
                      rfl

theorem cell22_2587296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 1, 5].length) (baseStart_2587296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2587296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2587296 prefixEnd_2587296 := by exact prefixLift 2587296
  have htrace : WordTrace (prefixWord ++ tailWord_2587296) baseStart_2587296 baseEnd_2587296 := by
    simpa [prefixWord, tailWord_2587296, baseEnd_2587296] using wordTrace_append hprefix tailTrace_2587296
  have hstable : (prefixWord ++ tailWord_2587296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587296).length < 2 ^ (prefixWord ++ tailWord_2587296).sum := by decide
  have hdescent : baseEnd_2587296 < baseStart_2587296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587305 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 4, 6]
def baseStart_2587305 : Nat := 118140960795 + 2587305 * 2 ^ 59
def prefixEnd_2587305 : Nat := 4983230072969 + 3 ^ 40 * 2587305 * 2
def baseEnd_2587305 : Nat := 885687376520736593992471

theorem tailTrace_2587305 : CollatzResearch.WordTrace tailWord_2587305 prefixEnd_2587305 885687376520736593992471 := by
  unfold tailWord_2587305
  simp only [CollatzResearch.WordTrace]
  refine ⟨94366765891643336359523369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62911177261095557573015579 94366765891643336359523369)
  ·
    refine ⟨70775074418732502269642527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94366765891643336359523369 70775074418732502269642527)
    ·
      refine ⟨106162611628098753404463791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70775074418732502269642527 106162611628098753404463791)
      ·
        refine ⟨159243917442148130106695687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106162611628098753404463791 159243917442148130106695687)
        ·
          refine ⟨238865876163222195160043531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159243917442148130106695687 238865876163222195160043531)
          ·
            refine ⟨358298814244833292740065297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238865876163222195160043531 358298814244833292740065297)
            ·
              refine ⟨268724110683624969555048973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 358298814244833292740065297 268724110683624969555048973)
              ·
                refine ⟨100771541506359363583143365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 268724110683624969555048973 100771541506359363583143365)
                ·
                  refine ⟨18894664032442380671839381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100771541506359363583143365 18894664032442380671839381)
                  ·
                    refine ⟨885687376520736593992471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18894664032442380671839381 885687376520736593992471)
                    ·
                      rfl

theorem cell22_2587305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 6].length) (baseStart_2587305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2587305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2587305 prefixEnd_2587305 := by exact prefixLift 2587305
  have htrace : WordTrace (prefixWord ++ tailWord_2587305) baseStart_2587305 baseEnd_2587305 := by
    simpa [prefixWord, tailWord_2587305, baseEnd_2587305] using wordTrace_append hprefix tailTrace_2587305
  have hstable : (prefixWord ++ tailWord_2587305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587305).length < 2 ^ (prefixWord ++ tailWord_2587305).sum := by decide
  have hdescent : baseEnd_2587305 < baseStart_2587305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587309 : List Nat := [1, 5, 2, 1, 1, 2, 4, 6]
def baseStart_2587309 : Nat := 118140960795 + 2587309 * 2 ^ 59
def prefixEnd_2587309 : Nat := 4983230072969 + 3 ^ 40 * 2587309 * 2
def baseEnd_2587309 : Nat := 98409860644720212988051

theorem tailTrace_2587309 : CollatzResearch.WordTrace tailWord_2587309 prefixEnd_2587309 98409860644720212988051 := by
  unfold tailWord_2587309
  simp only [CollatzResearch.WordTrace]
  refine ⟨94366911783628845042668981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62911274522419230028445987 94366911783628845042668981)
  ·
    refine ⟨8846897979715204222750217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94366911783628845042668981 8846897979715204222750217)
    ·
      refine ⟨6635173484786403167062663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8846897979715204222750217 6635173484786403167062663)
      ·
        refine ⟨9952760227179604750593995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6635173484786403167062663 9952760227179604750593995)
        ·
          refine ⟨14929140340769407125890993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9952760227179604750593995 14929140340769407125890993)
          ·
            refine ⟨11196855255577055344418245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14929140340769407125890993 11196855255577055344418245)
            ·
              refine ⟨2099410360420697877078421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11196855255577055344418245 2099410360420697877078421)
              ·
                refine ⟨98409860644720212988051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2099410360420697877078421 98409860644720212988051)
                ·
                  rfl

theorem cell22_2587309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 6].length) (baseStart_2587309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2587309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2587309 prefixEnd_2587309 := by exact prefixLift 2587309
  have htrace : WordTrace (prefixWord ++ tailWord_2587309) baseStart_2587309 baseEnd_2587309 := by
    simpa [prefixWord, tailWord_2587309, baseEnd_2587309] using wordTrace_append hprefix tailTrace_2587309
  have hstable : (prefixWord ++ tailWord_2587309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587309).length < 2 ^ (prefixWord ++ tailWord_2587309).sum := by decide
  have hdescent : baseEnd_2587309 < baseStart_2587309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587493 : List Nat := [1, 3, 1, 3, 1, 1, 5, 3, 1, 3]
def baseStart_2587493 : Nat := 118140960795 + 2587493 * 2 ^ 59
def prefixEnd_2587493 : Nat := 4983230072969 + 3 ^ 40 * 2587493 * 2
def baseEnd_2587493 : Nat := 885751732762766770291895

theorem tailTrace_2587493 : CollatzResearch.WordTrace tailWord_2587493 prefixEnd_2587493 885751732762766770291895 := by
  unfold tailWord_2587493
  simp only [CollatzResearch.WordTrace]
  refine ⟨94373622814962244467367133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62915748543308162978244755 94373622814962244467367133)
  ·
    refine ⟨35390108555610841675262675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94373622814962244467367133 35390108555610841675262675)
    ·
      refine ⟨53085162833416262512894013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35390108555610841675262675 53085162833416262512894013)
      ·
        refine ⟨19906936062531098442335255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53085162833416262512894013 19906936062531098442335255)
        ·
          refine ⟨29860404093796647663502883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19906936062531098442335255 29860404093796647663502883)
          ·
            refine ⟨44790606140694971495254325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29860404093796647663502883 44790606140694971495254325)
            ·
              refine ⟨4199119325690153577680093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44790606140694971495254325 4199119325690153577680093)
              ·
                refine ⟨1574669747133807591630035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4199119325690153577680093 1574669747133807591630035)
                ·
                  refine ⟨2362004620700711387445053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1574669747133807591630035 2362004620700711387445053)
                  ·
                    refine ⟨885751732762766770291895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2362004620700711387445053 885751732762766770291895)
                    ·
                      rfl

theorem cell22_2587493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 3, 1, 3].length) (baseStart_2587493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2587493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2587493 prefixEnd_2587493 := by exact prefixLift 2587493
  have htrace : WordTrace (prefixWord ++ tailWord_2587493) baseStart_2587493 baseEnd_2587493 := by
    simpa [prefixWord, tailWord_2587493, baseEnd_2587493] using wordTrace_append hprefix tailTrace_2587493
  have hstable : (prefixWord ++ tailWord_2587493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587493).length < 2 ^ (prefixWord ++ tailWord_2587493).sum := by decide
  have hdescent : baseEnd_2587493 < baseStart_2587493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587510 : List Nat := [5, 1, 1, 3, 1, 3, 1, 1, 3, 3]
def baseStart_2587510 : Nat := 118140960795 + 2587510 * 2 ^ 59
def prefixEnd_2587510 : Nat := 4983230072969 + 3 ^ 40 * 2587510 * 2
def baseEnd_2587510 : Nat := 885757552210184392616843

theorem tailTrace_2587510 : CollatzResearch.WordTrace tailWord_2587510 prefixEnd_2587510 885757552210184392616843 := by
  unfold tailWord_2587510
  simp only [CollatzResearch.WordTrace]
  refine ⟨5898390178493791023170999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62916161903933770913823989 5898390178493791023170999)
  ·
    refine ⟨8847585267740686534756499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5898390178493791023170999 8847585267740686534756499)
    ·
      refine ⟨13271377901611029802134749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8847585267740686534756499 13271377901611029802134749)
      ·
        refine ⟨4976766713104136175800531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13271377901611029802134749 4976766713104136175800531)
        ·
          refine ⟨7465150069656204263700797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4976766713104136175800531 7465150069656204263700797)
          ·
            refine ⟨2799431276121076598887799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7465150069656204263700797 2799431276121076598887799)
            ·
              refine ⟨4199146914181614898331699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2799431276121076598887799 4199146914181614898331699)
              ·
                refine ⟨6298720371272422347497549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4199146914181614898331699 6298720371272422347497549)
                ·
                  refine ⟨2362020139227158380311581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6298720371272422347497549 2362020139227158380311581)
                  ·
                    refine ⟨885757552210184392616843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2362020139227158380311581 885757552210184392616843)
                    ·
                      rfl

theorem cell22_2587510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_2587510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2587510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2587510 prefixEnd_2587510 := by exact prefixLift 2587510
  have htrace : WordTrace (prefixWord ++ tailWord_2587510) baseStart_2587510 baseEnd_2587510 := by
    simpa [prefixWord, tailWord_2587510, baseEnd_2587510] using wordTrace_append hprefix tailTrace_2587510
  have hstable : (prefixWord ++ tailWord_2587510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587510).length < 2 ^ (prefixWord ++ tailWord_2587510).sum := by decide
  have hdescent : baseEnd_2587510 < baseStart_2587510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587596 : List Nat := [2, 2, 1, 4, 1, 1, 5, 6]
def baseStart_2587596 : Nat := 118140960795 + 2587596 * 2 ^ 59
def prefixEnd_2587596 : Nat := 4983230072969 + 3 ^ 40 * 2587596 * 2
def baseEnd_2587596 : Nat := 98420776863078759440731

theorem tailTrace_2587596 : CollatzResearch.WordTrace tailWord_2587596 prefixEnd_2587596 98420776863078759440731 := by
  unfold tailWord_2587596
  simp only [CollatzResearch.WordTrace]
  refine ⟨47188689766794546529183321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62918253022392728705577761 47188689766794546529183321)
  ·
    refine ⟨35391517325095909896887491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47188689766794546529183321 35391517325095909896887491)
    ·
      refine ⟨53087275987643864845331237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35391517325095909896887491 53087275987643864845331237)
      ·
        refine ⟨9953864247683224658499607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53087275987643864845331237 9953864247683224658499607)
        ·
          refine ⟨14930796371524836987749411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9953864247683224658499607 14930796371524836987749411)
          ·
            refine ⟨22396194557287255481624117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14930796371524836987749411 22396194557287255481624117)
            ·
              refine ⟨2099643239745680201402261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22396194557287255481624117 2099643239745680201402261)
              ·
                refine ⟨98420776863078759440731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2099643239745680201402261 98420776863078759440731)
                ·
                  rfl

theorem cell22_2587596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 6].length) (baseStart_2587596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2587596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2587596 prefixEnd_2587596 := by exact prefixLift 2587596
  have htrace : WordTrace (prefixWord ++ tailWord_2587596) baseStart_2587596 baseEnd_2587596 := by
    simpa [prefixWord, tailWord_2587596, baseEnd_2587596] using wordTrace_append hprefix tailTrace_2587596
  have hstable : (prefixWord ++ tailWord_2587596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587596).length < 2 ^ (prefixWord ++ tailWord_2587596).sum := by decide
  have hdescent : baseEnd_2587596 < baseStart_2587596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587598 : List Nat := [4, 1, 1, 1, 2, 5, 1, 1, 2, 4]
def baseStart_2587598 : Nat := 118140960795 + 2587598 * 2 ^ 59
def prefixEnd_2587598 : Nat := 4983230072969 + 3 ^ 40 * 2587598 * 2
def baseEnd_2587598 : Nat := 885787676408581496416573

theorem tailTrace_2587598 : CollatzResearch.WordTrace tailWord_2587598 prefixEnd_2587598 885787676408581496416573 := by
  unfold tailWord_2587598
  simp only [CollatzResearch.WordTrace]
  refine ⟨11797181559947730924992431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62918301653054564933292965 11797181559947730924992431)
  ·
    refine ⟨17695772339921596387488647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11797181559947730924992431 17695772339921596387488647)
    ·
      refine ⟨26543658509882394581232971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17695772339921596387488647 26543658509882394581232971)
      ·
        refine ⟨39815487764823591871849457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26543658509882394581232971 39815487764823591871849457)
        ·
          refine ⟨29861615823617693903887093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39815487764823591871849457 29861615823617693903887093)
          ·
            refine ⟨2799526483464158803489415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29861615823617693903887093 2799526483464158803489415)
            ·
              refine ⟨4199289725196238205234123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2799526483464158803489415 4199289725196238205234123)
              ·
                refine ⟨6298934587794357307851185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4199289725196238205234123 6298934587794357307851185)
                ·
                  refine ⟨4724200940845767980888389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6298934587794357307851185 4724200940845767980888389)
                  ·
                    refine ⟨885787676408581496416573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4724200940845767980888389 885787676408581496416573)
                    ·
                      rfl

theorem cell22_2587598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 2, 4].length) (baseStart_2587598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2587598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2587598 prefixEnd_2587598 := by exact prefixLift 2587598
  have htrace : WordTrace (prefixWord ++ tailWord_2587598) baseStart_2587598 baseEnd_2587598 := by
    simpa [prefixWord, tailWord_2587598, baseEnd_2587598] using wordTrace_append hprefix tailTrace_2587598
  have hstable : (prefixWord ++ tailWord_2587598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587598).length < 2 ^ (prefixWord ++ tailWord_2587598).sum := by decide
  have hdescent : baseEnd_2587598 < baseStart_2587598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587662 : List Nat := [4, 1, 1, 2, 2, 4, 1, 3, 1, 3]
def baseStart_2587662 : Nat := 118140960795 + 2587662 * 2 ^ 59
def prefixEnd_2587662 : Nat := 4983230072969 + 3 ^ 40 * 2587662 * 2
def baseEnd_2587662 : Nat := 885809584916506662816377

theorem tailTrace_2587662 : CollatzResearch.WordTrace tailWord_2587662 prefixEnd_2587662 885809584916506662816377 := by
  unfold tailWord_2587662
  simp only [CollatzResearch.WordTrace]
  refine ⟨11797473343918748291283655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62919857834233324220179493 11797473343918748291283655)
  ·
    refine ⟨17696210015878122436925483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11797473343918748291283655 17696210015878122436925483)
    ·
      refine ⟨26544315023817183655388225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17696210015878122436925483 26544315023817183655388225)
      ·
        refine ⟨19908236267862887741541169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26544315023817183655388225 19908236267862887741541169)
        ·
          refine ⟨14931177200897165806155877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19908236267862887741541169 14931177200897165806155877)
          ·
            refine ⟨2799595725168218588654227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14931177200897165806155877 2799595725168218588654227)
            ·
              refine ⟨4199393587752327882981341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2799595725168218588654227 4199393587752327882981341)
              ·
                refine ⟨1574772595407122956118003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4199393587752327882981341 1574772595407122956118003)
                ·
                  refine ⟨2362158893110684434177005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1574772595407122956118003 2362158893110684434177005)
                  ·
                    refine ⟨885809584916506662816377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2362158893110684434177005 885809584916506662816377)
                    ·
                      rfl

theorem cell22_2587662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 3, 1, 3].length) (baseStart_2587662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2587662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2587662 prefixEnd_2587662 := by exact prefixLift 2587662
  have htrace : WordTrace (prefixWord ++ tailWord_2587662) baseStart_2587662 baseEnd_2587662 := by
    simpa [prefixWord, tailWord_2587662, baseEnd_2587662] using wordTrace_append hprefix tailTrace_2587662
  have hstable : (prefixWord ++ tailWord_2587662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587662).length < 2 ^ (prefixWord ++ tailWord_2587662).sum := by decide
  have hdescent : baseEnd_2587662 < baseStart_2587662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587701 : List Nat := [1, 3, 3, 1, 1, 1, 1, 5, 1, 5]
def baseStart_2587701 : Nat := 118140960795 + 2587701 * 2 ^ 59
def prefixEnd_2587701 : Nat := 4983230072969 + 3 ^ 40 * 2587701 * 2
def baseEnd_2587701 : Nat := 885822935413523561091257

theorem tailTrace_2587701 : CollatzResearch.WordTrace tailWord_2587701 prefixEnd_2587701 885822935413523561091257 := by
  unfold tailWord_2587701
  simp only [CollatzResearch.WordTrace]
  refine ⟨94381209198208695990938957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62920806132139130660625971 94381209198208695990938957)
  ·
    refine ⟨35392953449328260996602109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94381209198208695990938957 35392953449328260996602109)
    ·
      refine ⟨13272357543498097873725791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35392953449328260996602109 13272357543498097873725791)
      ·
        refine ⟨19908536315247146810588687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13272357543498097873725791 19908536315247146810588687)
        ·
          refine ⟨29862804472870720215883031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19908536315247146810588687 29862804472870720215883031)
          ·
            refine ⟨44794206709306080323824547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29862804472870720215883031 44794206709306080323824547)
            ·
              refine ⟨67191310063959120485736821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44794206709306080323824547 67191310063959120485736821)
              ·
                refine ⟨6299185318496167545537827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67191310063959120485736821 6299185318496167545537827)
                ·
                  refine ⟨9448777977744251318306741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6299185318496167545537827 9448777977744251318306741)
                  ·
                    refine ⟨885822935413523561091257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9448777977744251318306741 885822935413523561091257)
                    ·
                      rfl

theorem cell22_2587701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_2587701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2587701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2587701 prefixEnd_2587701 := by exact prefixLift 2587701
  have htrace : WordTrace (prefixWord ++ tailWord_2587701) baseStart_2587701 baseEnd_2587701 := by
    simpa [prefixWord, tailWord_2587701, baseEnd_2587701] using wordTrace_append hprefix tailTrace_2587701
  have hstable : (prefixWord ++ tailWord_2587701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587701).length < 2 ^ (prefixWord ++ tailWord_2587701).sum := by decide
  have hdescent : baseEnd_2587701 < baseStart_2587701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587705 : List Nat := [1, 2, 1, 5, 2, 3, 1, 2, 1, 4]
def baseStart_2587705 : Nat := 118140960795 + 2587705 * 2 ^ 59
def prefixEnd_2587705 : Nat := 4983230072969 + 3 ^ 40 * 2587705 * 2
def baseEnd_2587705 : Nat := 885824304695268883991245

theorem tailTrace_2587705 : CollatzResearch.WordTrace tailWord_2587705 prefixEnd_2587705 885824304695268883991245 := by
  unfold tailWord_2587705
  simp only [CollatzResearch.WordTrace]
  refine ⟨94381355090194204674084569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62920903393462803116056379 94381355090194204674084569)
  ·
    refine ⟨70786016317645653505563427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94381355090194204674084569 70786016317645653505563427)
    ·
      refine ⟨106179024476468480258345141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70786016317645653505563427 106179024476468480258345141)
      ·
        refine ⟨9954283544668920024219857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106179024476468480258345141 9954283544668920024219857)
        ·
          refine ⟨7465712658501690018164893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9954283544668920024219857 7465712658501690018164893)
          ·
            refine ⟨2799642246938133756811835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7465712658501690018164893 2799642246938133756811835)
            ·
              refine ⟨4199463370407200635217753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2799642246938133756811835 4199463370407200635217753)
              ·
                refine ⟨3149597527805400476413315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4199463370407200635217753 3149597527805400476413315)
                ·
                  refine ⟨4724396291708100714619973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3149597527805400476413315 4724396291708100714619973)
                  ·
                    refine ⟨885824304695268883991245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4724396291708100714619973 885824304695268883991245)
                    ·
                      rfl

theorem cell22_2587705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 2, 1, 4].length) (baseStart_2587705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2587705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2587705 prefixEnd_2587705 := by exact prefixLift 2587705
  have htrace : WordTrace (prefixWord ++ tailWord_2587705) baseStart_2587705 baseEnd_2587705 := by
    simpa [prefixWord, tailWord_2587705, baseEnd_2587705] using wordTrace_append hprefix tailTrace_2587705
  have hstable : (prefixWord ++ tailWord_2587705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587705).length < 2 ^ (prefixWord ++ tailWord_2587705).sum := by decide
  have hdescent : baseEnd_2587705 < baseStart_2587705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587823 : List Nat := [1, 1, 2, 1, 2, 3, 3, 4, 1, 4]
def baseStart_2587823 : Nat := 118140960795 + 2587823 * 2 ^ 59
def prefixEnd_2587823 : Nat := 4983230072969 + 3 ^ 40 * 2587823 * 2
def baseEnd_2587823 : Nat := 885864698506755909540883

theorem tailTrace_2587823 : CollatzResearch.WordTrace tailWord_2587823 prefixEnd_2587823 885864698506755909540883 := by
  unfold tailWord_2587823
  simp only [CollatzResearch.WordTrace]
  refine ⟨94385658903766710826880123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62923772602511140551253415 94385658903766710826880123)
  ·
    refine ⟨141578488355650066240320185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94385658903766710826880123 141578488355650066240320185)
    ·
      refine ⟨106183866266737549680240139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141578488355650066240320185 106183866266737549680240139)
      ·
        refine ⟨159275799400106324520360209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106183866266737549680240139 159275799400106324520360209)
        ·
          refine ⟨119456849550079743390270157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159275799400106324520360209 119456849550079743390270157)
          ·
            refine ⟨44796318581279903771351309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119456849550079743390270157 44796318581279903771351309)
            ·
              refine ⟨16798619467979963914256741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44796318581279903771351309 16798619467979963914256741)
              ·
                refine ⟨3149741150246243233923139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16798619467979963914256741 3149741150246243233923139)
                ·
                  refine ⟨4724611725369364850884709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3149741150246243233923139 4724611725369364850884709)
                  ·
                    refine ⟨885864698506755909540883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4724611725369364850884709 885864698506755909540883)
                    ·
                      rfl

theorem cell22_2587823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 4, 1, 4].length) (baseStart_2587823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2587823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2587823 prefixEnd_2587823 := by exact prefixLift 2587823
  have htrace : WordTrace (prefixWord ++ tailWord_2587823) baseStart_2587823 baseEnd_2587823 := by
    simpa [prefixWord, tailWord_2587823, baseEnd_2587823] using wordTrace_append hprefix tailTrace_2587823
  have hstable : (prefixWord ++ tailWord_2587823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587823).length < 2 ^ (prefixWord ++ tailWord_2587823).sum := by decide
  have hdescent : baseEnd_2587823 < baseStart_2587823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587851 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 3, 6]
def baseStart_2587851 : Nat := 118140960795 + 2587851 * 2 ^ 59
def prefixEnd_2587851 : Nat := 4983230072969 + 3 ^ 40 * 2587851 * 2
def baseEnd_2587851 : Nat := 885874283478973169840797

theorem tailTrace_2587851 : CollatzResearch.WordTrace tailWord_2587851 prefixEnd_2587851 885874283478973169840797 := by
  unfold tailWord_2587851
  simp only [CollatzResearch.WordTrace]
  refine ⟨94386680147665271608899407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62924453431776847739266271 94386680147665271608899407)
  ·
    refine ⟨141580020221497907413349111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94386680147665271608899407 141580020221497907413349111)
    ·
      refine ⟨212370030332246861120023667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141580020221497907413349111 212370030332246861120023667)
      ·
        refine ⟨318555045498370291680035501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212370030332246861120023667 318555045498370291680035501)
        ·
          refine ⟨119458142061888859380013313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 318555045498370291680035501 119458142061888859380013313)
          ·
            refine ⟨89593606546416644535009985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119458142061888859380013313 89593606546416644535009985)
            ·
              refine ⟨67195204909812483401257489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89593606546416644535009985 67195204909812483401257489)
              ·
                refine ⟨50396403682359362550943117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67195204909812483401257489 50396403682359362550943117)
                ·
                  refine ⟨18898651380884760956603669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50396403682359362550943117 18898651380884760956603669)
                  ·
                    refine ⟨885874283478973169840797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18898651380884760956603669 885874283478973169840797)
                    ·
                      rfl

theorem cell22_2587851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 6].length) (baseStart_2587851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2587851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2587851 prefixEnd_2587851 := by exact prefixLift 2587851
  have htrace : WordTrace (prefixWord ++ tailWord_2587851) baseStart_2587851 baseEnd_2587851 := by
    simpa [prefixWord, tailWord_2587851, baseEnd_2587851] using wordTrace_append hprefix tailTrace_2587851
  have hstable : (prefixWord ++ tailWord_2587851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587851).length < 2 ^ (prefixWord ++ tailWord_2587851).sum := by decide
  have hdescent : baseEnd_2587851 < baseStart_2587851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587885 : List Nat := [1, 5, 1, 2, 2, 1, 1, 3, 2, 4]
def baseStart_2587885 : Nat := 118140960795 + 2587885 * 2 ^ 59
def prefixEnd_2587885 : Nat := 4983230072969 + 3 ^ 40 * 2587885 * 2
def baseEnd_2587885 : Nat := 885885922373808414490693

theorem tailTrace_2587885 : CollatzResearch.WordTrace tailWord_2587885 prefixEnd_2587885 885885922373808414490693 := by
  unfold tailWord_2587885
  simp only [CollatzResearch.WordTrace]
  refine ⟨94387920229542095415637109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62925280153028063610424739 94387920229542095415637109)
  ·
    refine ⟨8848867521519571445215979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94387920229542095415637109 8848867521519571445215979)
    ·
      refine ⟨13273301282279357167823969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8848867521519571445215979 13273301282279357167823969)
      ·
        refine ⟨9954975961709517875867977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13273301282279357167823969 9954975961709517875867977)
        ·
          refine ⟨7466231971282138406900983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9954975961709517875867977 7466231971282138406900983)
          ·
            refine ⟨11199347956923207610351475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7466231971282138406900983 11199347956923207610351475)
            ·
              refine ⟨16799021935384811415527213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11199347956923207610351475 16799021935384811415527213)
              ·
                refine ⟨6299633225769304280822705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16799021935384811415527213 6299633225769304280822705)
                ·
                  refine ⟨4724724919326978210617029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6299633225769304280822705 4724724919326978210617029)
                  ·
                    refine ⟨885885922373808414490693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4724724919326978210617029 885885922373808414490693)
                    ·
                      rfl

theorem cell22_2587885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_2587885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2587885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2587885 prefixEnd_2587885 := by exact prefixLift 2587885
  have htrace : WordTrace (prefixWord ++ tailWord_2587885) baseStart_2587885 baseEnd_2587885 := by
    simpa [prefixWord, tailWord_2587885, baseEnd_2587885] using wordTrace_append hprefix tailTrace_2587885
  have hstable : (prefixWord ++ tailWord_2587885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587885).length < 2 ^ (prefixWord ++ tailWord_2587885).sum := by decide
  have hdescent : baseEnd_2587885 < baseStart_2587885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587906 : List Nat := [3, 4, 1, 1, 3, 2, 2, 2, 4]
def baseStart_2587906 : Nat := 118140960795 + 2587906 * 2 ^ 59
def prefixEnd_2587906 : Nat := 4983230072969 + 3 ^ 40 * 2587906 * 2
def baseEnd_2587906 : Nat := 295297703700990453238543

theorem tailTrace_2587906 : CollatzResearch.WordTrace tailWord_2587906 prefixEnd_2587906 295297703700990453238543 := by
  unfold tailWord_2587906
  simp only [CollatzResearch.WordTrace]
  refine ⟨23597171540616504000537893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62925790774977344001434381 23597171540616504000537893)
  ·
    refine ⟨4424469663865594500100855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23597171540616504000537893 4424469663865594500100855)
    ·
      refine ⟨6636704495798391750151283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4424469663865594500100855 6636704495798391750151283)
      ·
        refine ⟨9955056743697587625226925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6636704495798391750151283 9955056743697587625226925)
        ·
          refine ⟨3733146278886595359460097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9955056743697587625226925 3733146278886595359460097)
          ·
            refine ⟨2799859709164946519595073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3733146278886595359460097 2799859709164946519595073)
            ·
              refine ⟨2099894781873709889696305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2799859709164946519595073 2099894781873709889696305)
              ·
                refine ⟨1574921086405282417272229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2099894781873709889696305 1574921086405282417272229)
                ·
                  refine ⟨295297703700990453238543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1574921086405282417272229 295297703700990453238543)
                  ·
                    rfl

theorem cell22_2587906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_2587906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2587906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2587906 prefixEnd_2587906 := by exact prefixLift 2587906
  have htrace : WordTrace (prefixWord ++ tailWord_2587906) baseStart_2587906 baseEnd_2587906 := by
    simpa [prefixWord, tailWord_2587906, baseEnd_2587906] using wordTrace_append hprefix tailTrace_2587906
  have hstable : (prefixWord ++ tailWord_2587906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587906).length < 2 ^ (prefixWord ++ tailWord_2587906).sum := by decide
  have hdescent : baseEnd_2587906 < baseStart_2587906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587934 : List Nat := [4, 3, 2, 1, 2, 1, 3, 6]
def baseStart_2587934 : Nat := 118140960795 + 2587934 * 2 ^ 59
def prefixEnd_2587934 : Nat := 4983230072969 + 3 ^ 40 * 2587934 * 2
def baseEnd_2587934 : Nat := 98433632897243180001727

theorem tailTrace_2587934 : CollatzResearch.WordTrace tailWord_2587934 prefixEnd_2587934 98433632897243180001727 := by
  unfold tailWord_2587934
  simp only [CollatzResearch.WordTrace]
  refine ⟨11798713425795572098021357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62926471604243051189447237 11798713425795572098021357)
  ·
    refine ⟨4424517534673339536758009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11798713425795572098021357 4424517534673339536758009)
    ·
      refine ⟨3318388151005004652568507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4424517534673339536758009 3318388151005004652568507)
      ·
        refine ⟨4977582226507506978852761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3318388151005004652568507 4977582226507506978852761)
        ·
          refine ⟨3733186669880630234139571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4977582226507506978852761 3733186669880630234139571)
          ·
            refine ⟨5599780004820945351209357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3733186669880630234139571 5599780004820945351209357)
            ·
              refine ⟨2099917501807854506703509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5599780004820945351209357 2099917501807854506703509)
              ·
                refine ⟨98433632897243180001727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2099917501807854506703509 98433632897243180001727)
                ·
                  rfl

theorem cell22_2587934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 6].length) (baseStart_2587934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2587934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2587934 prefixEnd_2587934 := by exact prefixLift 2587934
  have htrace : WordTrace (prefixWord ++ tailWord_2587934) baseStart_2587934 baseEnd_2587934 := by
    simpa [prefixWord, tailWord_2587934, baseEnd_2587934] using wordTrace_append hprefix tailTrace_2587934
  have hstable : (prefixWord ++ tailWord_2587934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587934).length < 2 ^ (prefixWord ++ tailWord_2587934).sum := by decide
  have hdescent : baseEnd_2587934 < baseStart_2587934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588005 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 6, 3]
def baseStart_2588005 : Nat := 118140960795 + 2588005 * 2 ^ 59
def prefixEnd_2588005 : Nat := 4983230072969 + 3 ^ 40 * 2588005 * 2
def baseEnd_2588005 : Nat := 885927000826168101490325

theorem tailTrace_2588005 : CollatzResearch.WordTrace tailWord_2588005 prefixEnd_2588005 885927000826168101490325 := by
  unfold tailWord_2588005
  simp only [CollatzResearch.WordTrace]
  refine ⟨94392296989107355910005469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62928197992738237273336979 94392296989107355910005469)
  ·
    refine ⟨35397111370915258466252051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94392296989107355910005469 35397111370915258466252051)
    ·
      refine ⟨53095667056372887699378077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35397111370915258466252051 53095667056372887699378077)
      ·
        refine ⟨19910875146139832887266779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53095667056372887699378077 19910875146139832887266779)
        ·
          refine ⟨29866312719209749330900169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19910875146139832887266779 29866312719209749330900169)
          ·
            refine ⟨22399734539407311998175127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29866312719209749330900169 22399734539407311998175127)
            ·
              refine ⟨33599601809110967997262691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22399734539407311998175127 33599601809110967997262691)
              ·
                refine ⟨50399402713666451995894037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33599601809110967997262691 50399402713666451995894037)
                ·
                  refine ⟨2362472002203114937307533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 50399402713666451995894037 2362472002203114937307533)
                  ·
                    refine ⟨885927000826168101490325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2362472002203114937307533 885927000826168101490325)
                    ·
                      rfl

theorem cell22_2588005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 6, 3].length) (baseStart_2588005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2588005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2588005 prefixEnd_2588005 := by exact prefixLift 2588005
  have htrace : WordTrace (prefixWord ++ tailWord_2588005) baseStart_2588005 baseEnd_2588005 := by
    simpa [prefixWord, tailWord_2588005, baseEnd_2588005] using wordTrace_append hprefix tailTrace_2588005
  have hstable : (prefixWord ++ tailWord_2588005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588005).length < 2 ^ (prefixWord ++ tailWord_2588005).sum := by decide
  have hdescent : baseEnd_2588005 < baseStart_2588005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588035 : List Nat := [1, 1, 1, 3, 5, 2, 2, 7]
def baseStart_2588035 : Nat := 118140960795 + 2588035 * 2 ^ 59
def prefixEnd_2588035 : Nat := 4983230072969 + 3 ^ 40 * 2588035 * 2
def baseEnd_2588035 : Nat := 98437474493250891471137

theorem tailTrace_2588035 : CollatzResearch.WordTrace tailWord_2588035 prefixEnd_2588035 98437474493250891471137 := by
  unfold tailWord_2588035
  simp only [CollatzResearch.WordTrace]
  refine ⟨94393391178998671033597559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62928927452665780689065039 94393391178998671033597559)
  ·
    refine ⟨141590086768498006550396339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94393391178998671033597559 141590086768498006550396339)
    ·
      refine ⟨212385130152747009825594509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141590086768498006550396339 212385130152747009825594509)
      ·
        refine ⟨79644423807280128684597941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212385130152747009825594509 79644423807280128684597941)
        ·
          refine ⟨7466664731932512064181057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79644423807280128684597941 7466664731932512064181057)
          ·
            refine ⟨5599998548949384048135793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7466664731932512064181057 5599998548949384048135793)
            ·
              refine ⟨4199998911712038036101845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5599998548949384048135793 4199998911712038036101845)
              ·
                refine ⟨98437474493250891471137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4199998911712038036101845 98437474493250891471137)
                ·
                  rfl

theorem cell22_2588035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 7].length) (baseStart_2588035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2588035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2588035 prefixEnd_2588035 := by exact prefixLift 2588035
  have htrace : WordTrace (prefixWord ++ tailWord_2588035) baseStart_2588035 baseEnd_2588035 := by
    simpa [prefixWord, tailWord_2588035, baseEnd_2588035] using wordTrace_append hprefix tailTrace_2588035
  have hstable : (prefixWord ++ tailWord_2588035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588035).length < 2 ^ (prefixWord ++ tailWord_2588035).sum := by decide
  have hdescent : baseEnd_2588035 < baseStart_2588035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588039 : List Nat := [1, 1, 4, 2, 2, 2, 4, 1, 2, 3]
def baseStart_2588039 : Nat := 118140960795 + 2588039 * 2 ^ 59
def prefixEnd_2588039 : Nat := 4983230072969 + 3 ^ 40 * 2588039 * 2
def baseEnd_2588039 : Nat := 885938639721003346140221

theorem tailTrace_2588039 : CollatzResearch.WordTrace tailWord_2588039 prefixEnd_2588039 885938639721003346140221 := by
  unfold tailWord_2588039
  simp only [CollatzResearch.WordTrace]
  refine ⟨94393537070984179716743171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62929024713989453144495447 94393537070984179716743171)
  ·
    refine ⟨141590305606476269575114757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94393537070984179716743171 141590305606476269575114757)
    ·
      refine ⟨26548182301214300545334017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141590305606476269575114757 26548182301214300545334017)
      ·
        refine ⟨19911136725910725409000513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26548182301214300545334017 19911136725910725409000513)
        ·
          refine ⟨14933352544433044056750385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19911136725910725409000513 14933352544433044056750385)
          ·
            refine ⟨11200014408324783042562789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14933352544433044056750385 11200014408324783042562789)
            ·
              refine ⟨2100002701560896820480523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11200014408324783042562789 2100002701560896820480523)
              ·
                refine ⟨3150004052341345230720785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2100002701560896820480523 3150004052341345230720785)
                ·
                  refine ⟨2362503039256008923040589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3150004052341345230720785 2362503039256008923040589)
                  ·
                    refine ⟨885938639721003346140221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2362503039256008923040589 885938639721003346140221)
                    ·
                      rfl

theorem cell22_2588039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 1, 2, 3].length) (baseStart_2588039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2588039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2588039 prefixEnd_2588039 := by exact prefixLift 2588039
  have htrace : WordTrace (prefixWord ++ tailWord_2588039) baseStart_2588039 baseEnd_2588039 := by
    simpa [prefixWord, tailWord_2588039, baseEnd_2588039] using wordTrace_append hprefix tailTrace_2588039
  have hstable : (prefixWord ++ tailWord_2588039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588039).length < 2 ^ (prefixWord ++ tailWord_2588039).sum := by decide
  have hdescent : baseEnd_2588039 < baseStart_2588039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588118 : List Nat := [5, 2, 1, 1, 1, 3, 2, 3, 1, 3]
def baseStart_2588118 : Nat := 118140960795 + 2588118 * 2 ^ 59
def prefixEnd_2588118 : Nat := 4983230072969 + 3 ^ 40 * 2588118 * 2
def baseEnd_2588118 : Nat := 885965683035473473414979

theorem tailTrace_2588118 : CollatzResearch.WordTrace tailWord_2588118 prefixEnd_2588118 885965683035473473414979 := by
  unfold tailWord_2588118
  simp only [CollatzResearch.WordTrace]
  refine ⟨5899776152356123513054313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62930945625131984139246005 5899776152356123513054313)
  ·
    refine ⟨4424832114267092634790735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5899776152356123513054313 4424832114267092634790735)
    ·
      refine ⟨6637248171400638952186103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4424832114267092634790735 6637248171400638952186103)
      ·
        refine ⟨9955872257100958428279155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6637248171400638952186103 9955872257100958428279155)
        ·
          refine ⟨14933808385651437642418733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9955872257100958428279155 14933808385651437642418733)
          ·
            refine ⟨5600178144619289115907025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14933808385651437642418733 5600178144619289115907025)
            ·
              refine ⟨4200133608464466836930269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5600178144619289115907025 4200133608464466836930269)
              ·
                refine ⟨1575050103174175063848851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4200133608464466836930269 1575050103174175063848851)
                ·
                  refine ⟨2362575154761262595773277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1575050103174175063848851 2362575154761262595773277)
                  ·
                    refine ⟨885965683035473473414979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2362575154761262595773277 885965683035473473414979)
                    ·
                      rfl

theorem cell22_2588118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_2588118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2588118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2588118 prefixEnd_2588118 := by exact prefixLift 2588118
  have htrace : WordTrace (prefixWord ++ tailWord_2588118) baseStart_2588118 baseEnd_2588118 := by
    simpa [prefixWord, tailWord_2588118, baseEnd_2588118] using wordTrace_append hprefix tailTrace_2588118
  have hstable : (prefixWord ++ tailWord_2588118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588118).length < 2 ^ (prefixWord ++ tailWord_2588118).sum := by decide
  have hdescent : baseEnd_2588118 < baseStart_2588118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588127 : List Nat := [1, 1, 2, 3, 3, 1, 3, 3, 1, 4]
def baseStart_2588127 : Nat := 118140960795 + 2588127 * 2 ^ 59
def prefixEnd_2588127 : Nat := 4983230072969 + 3 ^ 40 * 2588127 * 2
def baseEnd_2588127 : Nat := 885968763919400449939951

theorem tailTrace_2588127 : CollatzResearch.WordTrace tailWord_2588127 prefixEnd_2588127 885968763919400449939951 := by
  unfold tailWord_2588127
  simp only [CollatzResearch.WordTrace]
  refine ⟨94396746694665370745946635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62931164463110247163964423 94396746694665370745946635)
  ·
    refine ⟨141595120041998056118919953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94396746694665370745946635 141595120041998056118919953)
    ·
      refine ⟨106196340031498542089189965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141595120041998056118919953 106196340031498542089189965)
      ·
        refine ⟨39823627511811953283446237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106196340031498542089189965 39823627511811953283446237)
        ·
          refine ⟨14933860316929482481292339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39823627511811953283446237 14933860316929482481292339)
          ·
            refine ⟨22400790475394223721938509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14933860316929482481292339 22400790475394223721938509)
            ·
              refine ⟨8400296428272833895726941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22400790475394223721938509 8400296428272833895726941)
              ·
                refine ⟨3150111160602312710897603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8400296428272833895726941 3150111160602312710897603)
                ·
                  refine ⟨4725166740903469066346405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3150111160602312710897603 4725166740903469066346405)
                  ·
                    refine ⟨885968763919400449939951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4725166740903469066346405 885968763919400449939951)
                    ·
                      rfl

theorem cell22_2588127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 3, 1, 4].length) (baseStart_2588127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2588127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2588127 prefixEnd_2588127 := by exact prefixLift 2588127
  have htrace : WordTrace (prefixWord ++ tailWord_2588127) baseStart_2588127 baseEnd_2588127 := by
    simpa [prefixWord, tailWord_2588127, baseEnd_2588127] using wordTrace_append hprefix tailTrace_2588127
  have hstable : (prefixWord ++ tailWord_2588127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588127).length < 2 ^ (prefixWord ++ tailWord_2588127).sum := by decide
  have hdescent : baseEnd_2588127 < baseStart_2588127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588142 : List Nat := [4, 1, 2, 1, 2, 1, 4, 1, 6]
def baseStart_2588142 : Nat := 118140960795 + 2588142 * 2 ^ 59
def prefixEnd_2588142 : Nat := 4983230072969 + 3 ^ 40 * 2588142 * 2
def baseEnd_2588142 : Nat := 295324632908648470271635

theorem tailTrace_2588142 : CollatzResearch.WordTrace tailWord_2588142 prefixEnd_2588142 295324632908648470271635 := by
  unfold tailWord_2588142
  simp only [CollatzResearch.WordTrace]
  refine ⟨11799661723701378538467835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62931529193074018871828453 11799661723701378538467835)
  ·
    refine ⟨17699492585552067807701753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11799661723701378538467835 17699492585552067807701753)
    ·
      refine ⟨13274619439164050855776315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17699492585552067807701753 13274619439164050855776315)
      ·
        refine ⟨19911929158746076283664473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13274619439164050855776315 19911929158746076283664473)
        ·
          refine ⟨14933946869059557212748355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19911929158746076283664473 14933946869059557212748355)
          ·
            refine ⟨22400920303589335819122533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14933946869059557212748355 22400920303589335819122533)
            ·
              refine ⟨4200172556923000466085475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22400920303589335819122533 4200172556923000466085475)
              ·
                refine ⟨6300258835384500699128213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4200172556923000466085475 6300258835384500699128213)
                ·
                  refine ⟨295324632908648470271635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6300258835384500699128213 295324632908648470271635)
                  ·
                    rfl

theorem cell22_2588142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_2588142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2588142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2588142 prefixEnd_2588142 := by exact prefixLift 2588142
  have htrace : WordTrace (prefixWord ++ tailWord_2588142) baseStart_2588142 baseEnd_2588142 := by
    simpa [prefixWord, tailWord_2588142, baseEnd_2588142] using wordTrace_append hprefix tailTrace_2588142
  have hstable : (prefixWord ++ tailWord_2588142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588142).length < 2 ^ (prefixWord ++ tailWord_2588142).sum := by decide
  have hdescent : baseEnd_2588142 < baseStart_2588142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588155 : List Nat := [1, 1, 1, 1, 1, 3, 2, 4, 4, 4]
def baseStart_2588155 : Nat := 118140960795 + 2588155 * 2 ^ 59
def prefixEnd_2588155 : Nat := 4983230072969 + 3 ^ 40 * 2588155 * 2
def baseEnd_2588155 : Nat := 885978348891617710239865

theorem tailTrace_2588155 : CollatzResearch.WordTrace tailWord_2588155 prefixEnd_2588155 885978348891617710239865 := by
  unfold tailWord_2588155
  simp only [CollatzResearch.WordTrace]
  refine ⟨94397767938563931527965919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62931845292375954351977279 94397767938563931527965919)
  ·
    refine ⟨141596651907845897291948879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94397767938563931527965919 141596651907845897291948879)
    ·
      refine ⟨212394977861768845937923319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141596651907845897291948879 212394977861768845937923319)
      ·
        refine ⟨318592466792653268906884979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212394977861768845937923319 318592466792653268906884979)
        ·
          refine ⟨477888700188979903360327469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318592466792653268906884979 477888700188979903360327469)
          ·
            refine ⟨179208262570867463760122801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 477888700188979903360327469 179208262570867463760122801)
            ·
              refine ⟨134406196928150597820092101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179208262570867463760122801 134406196928150597820092101)
              ·
                refine ⟨25201161924028237091267269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 134406196928150597820092101 25201161924028237091267269)
                ·
                  refine ⟨4725217860755294454612613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25201161924028237091267269 4725217860755294454612613)
                  ·
                    refine ⟨885978348891617710239865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4725217860755294454612613 885978348891617710239865)
                    ·
                      rfl

theorem cell22_2588155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 4, 4].length) (baseStart_2588155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2588155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2588155 prefixEnd_2588155 := by exact prefixLift 2588155
  have htrace : WordTrace (prefixWord ++ tailWord_2588155) baseStart_2588155 baseEnd_2588155 := by
    simpa [prefixWord, tailWord_2588155, baseEnd_2588155] using wordTrace_append hprefix tailTrace_2588155
  have hstable : (prefixWord ++ tailWord_2588155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588155).length < 2 ^ (prefixWord ++ tailWord_2588155).sum := by decide
  have hdescent : baseEnd_2588155 < baseStart_2588155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588157 : List Nat := [1, 4, 1, 1, 1, 4, 3, 1, 1, 5]
def baseStart_2588157 : Nat := 118140960795 + 2588157 * 2 ^ 59
def prefixEnd_2588157 : Nat := 4983230072969 + 3 ^ 40 * 2588157 * 2
def baseEnd_2588157 : Nat := 885979033532490371689859

theorem tailTrace_2588157 : CollatzResearch.WordTrace tailWord_2588157 prefixEnd_2588157 885979033532490371689859 := by
  unfold tailWord_2588157
  simp only [CollatzResearch.WordTrace]
  refine ⟨94397840884556685869538725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62931893923037790579692483 94397840884556685869538725)
  ·
    refine ⟨17699595165854378600538511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94397840884556685869538725 17699595165854378600538511)
    ·
      refine ⟨26549392748781567900807767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17699595165854378600538511 26549392748781567900807767)
      ·
        refine ⟨39824089123172351851211651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26549392748781567900807767 39824089123172351851211651)
        ·
          refine ⟨59736133684758527776817477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39824089123172351851211651 59736133684758527776817477)
          ·
            refine ⟨11200525065892223958153277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59736133684758527776817477 11200525065892223958153277)
            ·
              refine ⟨4200196899709583984307479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11200525065892223958153277 4200196899709583984307479)
              ·
                refine ⟨6300295349564375976461219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4200196899709583984307479 6300295349564375976461219)
                ·
                  refine ⟨9450443024346563964691829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6300295349564375976461219 9450443024346563964691829)
                  ·
                    refine ⟨885979033532490371689859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9450443024346563964691829 885979033532490371689859)
                    ·
                      rfl

theorem cell22_2588157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_2588157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2588157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2588157 prefixEnd_2588157 := by exact prefixLift 2588157
  have htrace : WordTrace (prefixWord ++ tailWord_2588157) baseStart_2588157 baseEnd_2588157 := by
    simpa [prefixWord, tailWord_2588157, baseEnd_2588157] using wordTrace_append hprefix tailTrace_2588157
  have hstable : (prefixWord ++ tailWord_2588157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588157).length < 2 ^ (prefixWord ++ tailWord_2588157).sum := by decide
  have hdescent : baseEnd_2588157 < baseStart_2588157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588264 : List Nat := [2, 1, 4, 3, 1, 2, 1, 1, 2, 5]
def baseStart_2588264 : Nat := 118140960795 + 2588264 * 2 ^ 59
def prefixEnd_2588264 : Nat := 4983230072969 + 3 ^ 40 * 2588264 * 2
def baseEnd_2588264 : Nat := 886015661819177759264531

theorem tailTrace_2588264 : CollatzResearch.WordTrace tailWord_2588264 prefixEnd_2588264 886015661819177759264531 := by
  unfold tailWord_2588264
  simp only [CollatzResearch.WordTrace]
  refine ⟨47200871747584521571841923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62934495663446028762455897 47200871747584521571841923)
  ·
    refine ⟨70801307621376782357762885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47200871747584521571841923 70801307621376782357762885)
    ·
      refine ⟨13275245179008146692080541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70801307621376782357762885 13275245179008146692080541)
      ·
        refine ⟨4978216942128055009530203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13275245179008146692080541 4978216942128055009530203)
        ·
          refine ⟨7467325413192082514295305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4978216942128055009530203 7467325413192082514295305)
          ·
            refine ⟨5600494059894061885721479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7467325413192082514295305 5600494059894061885721479)
            ·
              refine ⟨8400741089841092828582219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5600494059894061885721479 8400741089841092828582219)
              ·
                refine ⟨12601111634761639242873329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8400741089841092828582219 12601111634761639242873329)
                ·
                  refine ⟨9450833726071229432154997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12601111634761639242873329 9450833726071229432154997)
                  ·
                    refine ⟨886015661819177759264531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9450833726071229432154997 886015661819177759264531)
                    ·
                      rfl

theorem cell22_2588264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_2588264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2588264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2588264 prefixEnd_2588264 := by exact prefixLift 2588264
  have htrace : WordTrace (prefixWord ++ tailWord_2588264) baseStart_2588264 baseEnd_2588264 := by
    simpa [prefixWord, tailWord_2588264, baseEnd_2588264] using wordTrace_append hprefix tailTrace_2588264
  have hstable : (prefixWord ++ tailWord_2588264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588264).length < 2 ^ (prefixWord ++ tailWord_2588264).sum := by decide
  have hdescent : baseEnd_2588264 < baseStart_2588264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588358 : List Nat := [6, 1, 2, 1, 1, 1, 1, 1, 4, 4]
def baseStart_2588358 : Nat := 118140960795 + 2588358 * 2 ^ 59
def prefixEnd_2588358 : Nat := 4983230072969 + 3 ^ 40 * 2588358 * 2
def baseEnd_2588358 : Nat := 886047839940192847414243

theorem tailTrace_2588358 : CollatzResearch.WordTrace tailWord_2588358 prefixEnd_2588358 886047839940192847414243 := by
  unfold tailWord_2588358
  simp only [CollatzResearch.WordTrace]
  refine ⟨2950161623650890537425179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 62936781304552331465070485 2950161623650890537425179)
  ·
    refine ⟨4425242435476335806137769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2950161623650890537425179 4425242435476335806137769)
    ·
      refine ⟨3318931826607251854603327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4425242435476335806137769 3318931826607251854603327)
      ·
        refine ⟨4978397739910877781904991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3318931826607251854603327 4978397739910877781904991)
        ·
          refine ⟨7467596609866316672857487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4978397739910877781904991 7467596609866316672857487)
          ·
            refine ⟨11201394914799475009286231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7467596609866316672857487 11201394914799475009286231)
            ·
              refine ⟨16802092372199212513929347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11201394914799475009286231 16802092372199212513929347)
              ·
                refine ⟨25203138558298818770894021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16802092372199212513929347 25203138558298818770894021)
                ·
                  refine ⟨4725588479681028519542629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25203138558298818770894021 4725588479681028519542629)
                  ·
                    refine ⟨886047839940192847414243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4725588479681028519542629 886047839940192847414243)
                    ·
                      rfl

theorem cell22_2588358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_2588358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2588358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2588358 prefixEnd_2588358 := by exact prefixLift 2588358
  have htrace : WordTrace (prefixWord ++ tailWord_2588358) baseStart_2588358 baseEnd_2588358 := by
    simpa [prefixWord, tailWord_2588358, baseEnd_2588358] using wordTrace_append hprefix tailTrace_2588358
  have hstable : (prefixWord ++ tailWord_2588358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588358).length < 2 ^ (prefixWord ++ tailWord_2588358).sum := by decide
  have hdescent : baseEnd_2588358 < baseStart_2588358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588474 : List Nat := [3, 1, 1, 1, 5, 2, 9]
def baseStart_2588474 : Nat := 118140960795 + 2588474 * 2 ^ 59
def prefixEnd_2588474 : Nat := 4983230072969 + 3 ^ 40 * 2588474 * 2
def baseEnd_2588474 : Nat := 32818057374474341167181

theorem tailTrace_2588474 : CollatzResearch.WordTrace tailWord_2588474 prefixEnd_2588474 32818057374474341167181 := by
  unfold tailWord_2588474
  simp only [CollatzResearch.WordTrace]
  refine ⟨23602350706102062252207119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62939601882938832672552317 23602350706102062252207119)
  ·
    refine ⟨35403526059153093378310679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23602350706102062252207119 35403526059153093378310679)
    ·
      refine ⟨53105289088729640067466019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35403526059153093378310679 53105289088729640067466019)
      ·
        refine ⟨79657933633094460101199029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53105289088729640067466019 79657933633094460101199029)
        ·
          refine ⟨7467931278102605634487409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79657933633094460101199029 7467931278102605634487409)
          ·
            refine ⟨5600948458576954225865557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7467931278102605634487409 5600948458576954225865557)
            ·
              refine ⟨32818057374474341167181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5600948458576954225865557 32818057374474341167181)
              ·
                rfl

theorem cell22_2588474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 9].length) (baseStart_2588474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2588474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2588474 prefixEnd_2588474 := by exact prefixLift 2588474
  have htrace : WordTrace (prefixWord ++ tailWord_2588474) baseStart_2588474 baseEnd_2588474 := by
    simpa [prefixWord, tailWord_2588474, baseEnd_2588474] using wordTrace_append hprefix tailTrace_2588474
  have hstable : (prefixWord ++ tailWord_2588474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588474).length < 2 ^ (prefixWord ++ tailWord_2588474).sum := by decide
  have hdescent : baseEnd_2588474 < baseStart_2588474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588478 : List Nat := [4, 2, 1, 2, 2, 2, 1, 1, 4, 3]
def baseStart_2588478 : Nat := 118140960795 + 2588478 * 2 ^ 59
def prefixEnd_2588478 : Nat := 4983230072969 + 3 ^ 40 * 2588478 * 2
def baseEnd_2588478 : Nat := 886088918392552534413875

theorem tailTrace_2588478 : CollatzResearch.WordTrace tailWord_2588478 prefixEnd_2588478 886088918392552534413875 := by
  unfold tailWord_2588478
  simp only [CollatzResearch.WordTrace]
  refine ⟨11801193589549219711496761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62939699144262505127982725 11801193589549219711496761)
  ·
    refine ⟨8850895192161914783622571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11801193589549219711496761 8850895192161914783622571)
    ·
      refine ⟨13276342788242872175433857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8850895192161914783622571 13276342788242872175433857)
      ·
        refine ⟨9957257091182154131575393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13276342788242872175433857 9957257091182154131575393)
        ·
          refine ⟨7467942818386615598681545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9957257091182154131575393 7467942818386615598681545)
          ·
            refine ⟨5600957113789961699011159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7467942818386615598681545 5600957113789961699011159)
            ·
              refine ⟨8401435670684942548516739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5600957113789961699011159 8401435670684942548516739)
              ·
                refine ⟨12602153506027413822775109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8401435670684942548516739 12602153506027413822775109)
                ·
                  refine ⟨2362903782380140091770333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12602153506027413822775109 2362903782380140091770333)
                  ·
                    refine ⟨886088918392552534413875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2362903782380140091770333 886088918392552534413875)
                    ·
                      rfl

theorem cell22_2588478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_2588478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2588478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2588478 prefixEnd_2588478 := by exact prefixLift 2588478
  have htrace : WordTrace (prefixWord ++ tailWord_2588478) baseStart_2588478 baseEnd_2588478 := by
    simpa [prefixWord, tailWord_2588478, baseEnd_2588478] using wordTrace_append hprefix tailTrace_2588478
  have hstable : (prefixWord ++ tailWord_2588478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588478).length < 2 ^ (prefixWord ++ tailWord_2588478).sum := by decide
  have hdescent : baseEnd_2588478 < baseStart_2588478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588506 : List Nat := [3, 1, 1, 2, 1, 3, 1, 4, 3, 3]
def baseStart_2588506 : Nat := 118140960795 + 2588506 * 2 ^ 59
def prefixEnd_2588506 : Nat := 4983230072969 + 3 ^ 40 * 2588506 * 2
def baseEnd_2588506 : Nat := 886098503364769794713789

theorem tailTrace_2588506 : CollatzResearch.WordTrace tailWord_2588506 prefixEnd_2588506 886098503364769794713789 := by
  unfold tailWord_2588506
  simp only [CollatzResearch.WordTrace]
  refine ⟨23602642490073079618498343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62940379973528212315995581 23602642490073079618498343)
  ·
    refine ⟨35403963735109619427747515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23602642490073079618498343 35403963735109619427747515)
    ·
      refine ⟨53105945602664429141621273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35403963735109619427747515 53105945602664429141621273)
      ·
        refine ⟨39829459201998321856215955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53105945602664429141621273 39829459201998321856215955)
        ·
          refine ⟨59744188802997482784323933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39829459201998321856215955 59744188802997482784323933)
          ·
            refine ⟨22404070801124056044121475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59744188802997482784323933 22404070801124056044121475)
            ·
              refine ⟨33606106201686084066182213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22404070801124056044121475 33606106201686084066182213)
              ·
                refine ⟨6301144912816140762409165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33606106201686084066182213 6301144912816140762409165)
                ·
                  refine ⟨2362929342306052785903437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6301144912816140762409165 2362929342306052785903437)
                  ·
                    refine ⟨886098503364769794713789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2362929342306052785903437 886098503364769794713789)
                    ·
                      rfl

theorem cell22_2588506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 3, 3].length) (baseStart_2588506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2588506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2588506 prefixEnd_2588506 := by exact prefixLift 2588506
  have htrace : WordTrace (prefixWord ++ tailWord_2588506) baseStart_2588506 baseEnd_2588506 := by
    simpa [prefixWord, tailWord_2588506, baseEnd_2588506] using wordTrace_append hprefix tailTrace_2588506
  have hstable : (prefixWord ++ tailWord_2588506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588506).length < 2 ^ (prefixWord ++ tailWord_2588506).sum := by decide
  have hdescent : baseEnd_2588506 < baseStart_2588506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588519 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 9]
def baseStart_2588519 : Nat := 118140960795 + 2588519 * 2 ^ 59
def prefixEnd_2588519 : Nat := 4983230072969 + 3 ^ 40 * 2588519 * 2
def baseEnd_2588519 : Nat := 295367651176814031379583

theorem tailTrace_2588519 : CollatzResearch.WordTrace tailWord_2588519 prefixEnd_2588519 295367651176814031379583 := by
  unfold tailWord_2588519
  simp only [CollatzResearch.WordTrace]
  refine ⟨94411044109245221694216611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62940696072830147796144407 94411044109245221694216611)
  ·
    refine ⟨141616566163867832541324917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94411044109245221694216611 141616566163867832541324917)
    ·
      refine ⟨13276553077862609300749211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 141616566163867832541324917 13276553077862609300749211)
      ·
        refine ⟨19914829616793913951123817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13276553077862609300749211 19914829616793913951123817)
        ·
          refine ⟨14936122212595435463342863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19914829616793913951123817 14936122212595435463342863)
          ·
            refine ⟨22404183318893153195014295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14936122212595435463342863 22404183318893153195014295)
            ·
              refine ⟨33606274978339729792521443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22404183318893153195014295 33606274978339729792521443)
              ·
                refine ⟨50409412467509594688782165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33606274978339729792521443 50409412467509594688782165)
                ·
                  refine ⟨295367651176814031379583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 50409412467509594688782165 295367651176814031379583)
                  ·
                    rfl

theorem cell22_2588519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 9].length) (baseStart_2588519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2588519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2588519 prefixEnd_2588519 := by exact prefixLift 2588519
  have htrace : WordTrace (prefixWord ++ tailWord_2588519) baseStart_2588519 baseEnd_2588519 := by
    simpa [prefixWord, tailWord_2588519, baseEnd_2588519] using wordTrace_append hprefix tailTrace_2588519
  have hstable : (prefixWord ++ tailWord_2588519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588519).length < 2 ^ (prefixWord ++ tailWord_2588519).sum := by decide
  have hdescent : baseEnd_2588519 < baseStart_2588519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588647 : List Nat := [1, 1, 5, 2, 3, 2, 1, 2, 2, 3]
def baseStart_2588647 : Nat := 118140960795 + 2588647 * 2 ^ 59
def prefixEnd_2588647 : Nat := 4983230072969 + 3 ^ 40 * 2588647 * 2
def baseEnd_2588647 : Nat := 886146770546292426938357

theorem tailTrace_2588647 : CollatzResearch.WordTrace tailWord_2588647 prefixEnd_2588647 886146770546292426938357 := by
  unfold tailWord_2588647
  simp only [CollatzResearch.WordTrace]
  refine ⟨94415712652781499554876195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62943808435187666369917463 94415712652781499554876195)
  ·
    refine ⟨141623568979172249332314293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94415712652781499554876195 141623568979172249332314293)
    ·
      refine ⟨13277209591797398374904465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 141623568979172249332314293 13277209591797398374904465)
      ·
        refine ⟨9957907193848048781178349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13277209591797398374904465 9957907193848048781178349)
        ·
          refine ⟨3734215197693018292941881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9957907193848048781178349 3734215197693018292941881)
          ·
            refine ⟨2800661398269763719706411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3734215197693018292941881 2800661398269763719706411)
            ·
              refine ⟨4200992097404645579559617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2800661398269763719706411 4200992097404645579559617)
              ·
                refine ⟨3150744073053484184669713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4200992097404645579559617 3150744073053484184669713)
                ·
                  refine ⟨2363058054790113138502285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3150744073053484184669713 2363058054790113138502285)
                  ·
                    refine ⟨886146770546292426938357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2363058054790113138502285 886146770546292426938357)
                    ·
                      rfl

theorem cell22_2588647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_2588647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2588647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2588647 prefixEnd_2588647 := by exact prefixLift 2588647
  have htrace : WordTrace (prefixWord ++ tailWord_2588647) baseStart_2588647 baseEnd_2588647 := by
    simpa [prefixWord, tailWord_2588647, baseEnd_2588647] using wordTrace_append hprefix tailTrace_2588647
  have hstable : (prefixWord ++ tailWord_2588647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588647).length < 2 ^ (prefixWord ++ tailWord_2588647).sum := by decide
  have hdescent : baseEnd_2588647 < baseStart_2588647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588671 : List Nat := [1, 1, 2, 2, 1, 2, 1, 7, 5]
def baseStart_2588671 : Nat := 118140960795 + 2588671 * 2 ^ 59
def prefixEnd_2588671 : Nat := 4983230072969 + 3 ^ 40 * 2588671 * 2
def baseEnd_2588671 : Nat := 295384995412254788112761

theorem tailTrace_2588671 : CollatzResearch.WordTrace tailWord_2588671 prefixEnd_2588671 295384995412254788112761 := by
  unfold tailWord_2588671
  simp only [CollatzResearch.WordTrace]
  refine ⟨94416588004694551653749867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62944392003129701102499911 94416588004694551653749867)
  ·
    refine ⟨141624882007041827480624801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94416588004694551653749867 141624882007041827480624801)
    ·
      refine ⟨106218661505281370610468601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141624882007041827480624801 106218661505281370610468601)
      ·
        refine ⟨79663996128961027957851451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106218661505281370610468601 79663996128961027957851451)
        ·
          refine ⟨119495994193441541936777177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79663996128961027957851451 119495994193441541936777177)
          ·
            refine ⟨89621995645081156452582883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119495994193441541936777177 89621995645081156452582883)
            ·
              refine ⟨134432993467621734678874325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89621995645081156452582883 134432993467621734678874325)
              ·
                refine ⟨3150773284397384406536117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 134432993467621734678874325 3150773284397384406536117)
                ·
                  refine ⟨295384995412254788112761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3150773284397384406536117 295384995412254788112761)
                  ·
                    rfl

theorem cell22_2588671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 7, 5].length) (baseStart_2588671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2588671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2588671 prefixEnd_2588671 := by exact prefixLift 2588671
  have htrace : WordTrace (prefixWord ++ tailWord_2588671) baseStart_2588671 baseEnd_2588671 := by
    simpa [prefixWord, tailWord_2588671, baseEnd_2588671] using wordTrace_append hprefix tailTrace_2588671
  have hstable : (prefixWord ++ tailWord_2588671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588671).length < 2 ^ (prefixWord ++ tailWord_2588671).sum := by decide
  have hdescent : baseEnd_2588671 < baseStart_2588671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588716 : List Nat := [2, 2, 1, 1, 1, 2, 2, 5, 6]
def baseStart_2588716 : Nat := 118140960795 + 2588716 * 2 ^ 59
def prefixEnd_2588716 : Nat := 4983230072969 + 3 ^ 40 * 2588716 * 2
def baseEnd_2588716 : Nat := 295390130218799748987715

theorem tailTrace_2588716 : CollatzResearch.WordTrace tailWord_2588716 prefixEnd_2588716 295390130218799748987715 := by
  unfold tailWord_2588716
  simp only [CollatzResearch.WordTrace]
  refine ⟨47209114644765762169569001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62945486193021016226092001 47209114644765762169569001)
  ·
    refine ⟨35406835983574321627176751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47209114644765762169569001 35406835983574321627176751)
    ·
      refine ⟨53110253975361482440765127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35406835983574321627176751 53110253975361482440765127)
      ·
        refine ⟨79665380963042223661147691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53110253975361482440765127 79665380963042223661147691)
        ·
          refine ⟨119498071444563335491721537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79665380963042223661147691 119498071444563335491721537)
          ·
            refine ⟨89623553583422501618791153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119498071444563335491721537 89623553583422501618791153)
            ·
              refine ⟨67217665187566876214093365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89623553583422501618791153 67217665187566876214093365)
              ·
                refine ⟨6301656111334394645071253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67217665187566876214093365 6301656111334394645071253)
                ·
                  refine ⟨295390130218799748987715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6301656111334394645071253 295390130218799748987715)
                  ·
                    rfl

theorem cell22_2588716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 6].length) (baseStart_2588716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2588716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2588716 prefixEnd_2588716 := by exact prefixLift 2588716
  have htrace : WordTrace (prefixWord ++ tailWord_2588716) baseStart_2588716 baseEnd_2588716 := by
    simpa [prefixWord, tailWord_2588716, baseEnd_2588716] using wordTrace_append hprefix tailTrace_2588716
  have hstable : (prefixWord ++ tailWord_2588716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588716).length < 2 ^ (prefixWord ++ tailWord_2588716).sum := by decide
  have hdescent : baseEnd_2588716 < baseStart_2588716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588748 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 6, 3]
def baseStart_2588748 : Nat := 118140960795 + 2588748 * 2 ^ 59
def prefixEnd_2588748 : Nat := 4983230072969 + 3 ^ 40 * 2588748 * 2
def baseEnd_2588748 : Nat := 886181344910361830163047

theorem tailTrace_2588748 : CollatzResearch.WordTrace tailWord_2588748 prefixEnd_2588748 886181344910361830163047 := by
  unfold tailWord_2588748
  simp only [CollatzResearch.WordTrace]
  refine ⟨47209698212707796902151449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62946264283610395869535265 47209698212707796902151449)
  ·
    refine ⟨35407273659530847676613587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47209698212707796902151449 35407273659530847676613587)
    ·
      refine ⟨53110910489296271514920381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35407273659530847676613587 53110910489296271514920381)
      ·
        refine ⟨19916591433486101818095143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53110910489296271514920381 19916591433486101818095143)
        ·
          refine ⟨29874887150229152727142715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19916591433486101818095143 29874887150229152727142715)
          ·
            refine ⟨44812330725343729090714073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29874887150229152727142715 44812330725343729090714073)
            ·
              refine ⟨33609248044007796818035555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44812330725343729090714073 33609248044007796818035555)
              ·
                refine ⟨50413872066011695227053333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33609248044007796818035555 50413872066011695227053333)
                ·
                  refine ⟨2363150253094298213768125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 50413872066011695227053333 2363150253094298213768125)
                  ·
                    refine ⟨886181344910361830163047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2363150253094298213768125 886181344910361830163047)
                    ·
                      rfl

theorem cell22_2588748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 6, 3].length) (baseStart_2588748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2588748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2588748 prefixEnd_2588748 := by exact prefixLift 2588748
  have htrace : WordTrace (prefixWord ++ tailWord_2588748) baseStart_2588748 baseEnd_2588748 := by
    simpa [prefixWord, tailWord_2588748, baseEnd_2588748] using wordTrace_append hprefix tailTrace_2588748
  have hstable : (prefixWord ++ tailWord_2588748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588748).length < 2 ^ (prefixWord ++ tailWord_2588748).sum := by decide
  have hdescent : baseEnd_2588748 < baseStart_2588748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588846 : List Nat := [4, 1, 4, 2, 2, 1, 2, 6]
def baseStart_2588846 : Nat := 118140960795 + 2588846 * 2 ^ 59
def prefixEnd_2588846 : Nat := 4983230072969 + 3 ^ 40 * 2588846 * 2
def baseEnd_2588846 : Nat := 98468321368124693468083

theorem tailTrace_2588846 : CollatzResearch.WordTrace tailWord_2588846 prefixEnd_2588846 98468321368124693468083 := by
  unfold tailWord_2588846
  simp only [CollatzResearch.WordTrace]
  refine ⟨11802871347382569567671299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62948647186040371027580261 11802871347382569567671299)
  ·
    refine ⟨17704307021073854351506949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11802871347382569567671299 17704307021073854351506949)
    ·
      refine ⟨3319557566451347690907553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17704307021073854351506949 3319557566451347690907553)
      ·
        refine ⟨2489668174838510768180665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3319557566451347690907553 2489668174838510768180665)
        ·
          refine ⟨1867251131128883076135499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2489668174838510768180665 1867251131128883076135499)
          ·
            refine ⟨2800876696693324614203249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1867251131128883076135499 2800876696693324614203249)
            ·
              refine ⟨2100657522519993460652437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2800876696693324614203249 2100657522519993460652437)
              ·
                refine ⟨98468321368124693468083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2100657522519993460652437 98468321368124693468083)
                ·
                  rfl

theorem cell22_2588846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 6].length) (baseStart_2588846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2588846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2588846 prefixEnd_2588846 := by exact prefixLift 2588846
  have htrace : WordTrace (prefixWord ++ tailWord_2588846) baseStart_2588846 baseEnd_2588846 := by
    simpa [prefixWord, tailWord_2588846, baseEnd_2588846] using wordTrace_append hprefix tailTrace_2588846
  have hstable : (prefixWord ++ tailWord_2588846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588846).length < 2 ^ (prefixWord ++ tailWord_2588846).sum := by decide
  have hdescent : baseEnd_2588846 < baseStart_2588846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588913 : List Nat := [1, 2, 2, 2, 2, 1, 4, 8]
def baseStart_2588913 : Nat := 118140960795 + 2588913 * 2 ^ 59
def prefixEnd_2588913 : Nat := 4983230072969 + 3 ^ 40 * 2588913 * 2
def baseEnd_2588913 : Nat := 98470869753595155531949

theorem tailTrace_2588913 : CollatzResearch.WordTrace tailWord_2588913 prefixEnd_2588913 98470869753595155531949 := by
  unfold tailWord_2588913
  simp only [CollatzResearch.WordTrace]
  refine ⟨94425414469817826984059393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62950276313211884656039595 94425414469817826984059393)
  ·
    refine ⟨70819060852363370238044545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94425414469817826984059393 70819060852363370238044545)
    ·
      refine ⟨53114295639272527678533409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70819060852363370238044545 53114295639272527678533409)
      ·
        refine ⟨39835721729454395758900057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53114295639272527678533409 39835721729454395758900057)
        ·
          refine ⟨29876791297090796819175043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39835721729454395758900057 29876791297090796819175043)
          ·
            refine ⟨44815186945636195228762565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29876791297090796819175043 44815186945636195228762565)
            ·
              refine ⟨8402847552306786605392981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44815186945636195228762565 8402847552306786605392981)
              ·
                refine ⟨98470869753595155531949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8402847552306786605392981 98470869753595155531949)
                ·
                  rfl

theorem cell22_2588913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 8].length) (baseStart_2588913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2588913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2588913 prefixEnd_2588913 := by exact prefixLift 2588913
  have htrace : WordTrace (prefixWord ++ tailWord_2588913) baseStart_2588913 baseEnd_2588913 := by
    simpa [prefixWord, tailWord_2588913, baseEnd_2588913] using wordTrace_append hprefix tailTrace_2588913
  have hstable : (prefixWord ++ tailWord_2588913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588913).length < 2 ^ (prefixWord ++ tailWord_2588913).sum := by decide
  have hdescent : baseEnd_2588913 < baseStart_2588913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588915 : List Nat := [1, 1, 1, 2, 2, 4, 4, 1, 2, 4]
def baseStart_2588915 : Nat := 118140960795 + 2588915 * 2 ^ 59
def prefixEnd_2588915 : Nat := 4983230072969 + 3 ^ 40 * 2588915 * 2
def baseEnd_2588915 : Nat := 886238512423229061237535

theorem tailTrace_2588915 : CollatzResearch.WordTrace tailWord_2588915 prefixEnd_2588915 886238512423229061237535 := by
  unfold tailWord_2588915
  simp only [CollatzResearch.WordTrace]
  refine ⟨94425487415810581325632199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62950324943873720883754799 94425487415810581325632199)
  ·
    refine ⟨141638231123715871988448299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94425487415810581325632199 141638231123715871988448299)
    ·
      refine ⟨212457346685573807982672449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141638231123715871988448299 212457346685573807982672449)
      ·
        refine ⟨159343010014180355987004337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212457346685573807982672449 159343010014180355987004337)
        ·
          refine ⟨119507257510635266990253253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159343010014180355987004337 119507257510635266990253253)
          ·
            refine ⟨22407610783244112560672485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119507257510635266990253253 22407610783244112560672485)
            ·
              refine ⟨4201427021858271105126091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22407610783244112560672485 4201427021858271105126091)
              ·
                refine ⟨6302140532787406657689137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4201427021858271105126091 6302140532787406657689137)
                ·
                  refine ⟨4726605399590554993266853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6302140532787406657689137 4726605399590554993266853)
                  ·
                    refine ⟨886238512423229061237535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4726605399590554993266853 886238512423229061237535)
                    ·
                      rfl

theorem cell22_2588915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 2, 4].length) (baseStart_2588915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2588915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2588915 prefixEnd_2588915 := by exact prefixLift 2588915
  have htrace : WordTrace (prefixWord ++ tailWord_2588915) baseStart_2588915 baseEnd_2588915 := by
    simpa [prefixWord, tailWord_2588915, baseEnd_2588915] using wordTrace_append hprefix tailTrace_2588915
  have hstable : (prefixWord ++ tailWord_2588915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588915).length < 2 ^ (prefixWord ++ tailWord_2588915).sum := by decide
  have hdescent : baseEnd_2588915 < baseStart_2588915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588930 : List Nat := [3, 4, 1, 1, 2, 11]
def baseStart_2588930 : Nat := 118140960795 + 2588930 * 2 ^ 59
def prefixEnd_2588930 : Nat := 4983230072969 + 3 ^ 40 * 2588930 * 2
def baseEnd_2588930 : Nat := 10941279595429308914969

theorem tailTrace_2588930 : CollatzResearch.WordTrace tailWord_2588930 prefixEnd_2588930 10941279595429308914969 := by
  unfold tailWord_2588930
  simp only [CollatzResearch.WordTrace]
  refine ⟨23606508627689059721857061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62950689673837492591618829 23606508627689059721857061)
  ·
    refine ⟨4426220367691698697848199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23606508627689059721857061 4426220367691698697848199)
    ·
      refine ⟨6639330551537548046772299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4426220367691698697848199 6639330551537548046772299)
      ·
        refine ⟨9958995827306322070158449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6639330551537548046772299 9958995827306322070158449)
        ·
          refine ⟨7469246870479741552618837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9958995827306322070158449 7469246870479741552618837)
          ·
            refine ⟨10941279595429308914969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7469246870479741552618837 10941279595429308914969)
            ·
              rfl

theorem cell22_2588930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 11].length) (baseStart_2588930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2588930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2588930 prefixEnd_2588930 := by exact prefixLift 2588930
  have htrace : WordTrace (prefixWord ++ tailWord_2588930) baseStart_2588930 baseEnd_2588930 := by
    simpa [prefixWord, tailWord_2588930, baseEnd_2588930] using wordTrace_append hprefix tailTrace_2588930
  have hstable : (prefixWord ++ tailWord_2588930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588930).length < 2 ^ (prefixWord ++ tailWord_2588930).sum := by decide
  have hdescent : baseEnd_2588930 < baseStart_2588930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588962 : List Nat := [3, 3, 1, 1, 3, 1, 1, 1, 5, 3]
def baseStart_2588962 : Nat := 118140960795 + 2588962 * 2 ^ 59
def prefixEnd_2588962 : Nat := 4983230072969 + 3 ^ 40 * 2588962 * 2
def baseEnd_2588962 : Nat := 886254601483736605312391

theorem tailTrace_2588962 : CollatzResearch.WordTrace tailWord_2588962 prefixEnd_2588962 886254601483736605312391 := by
  unfold tailWord_2588962
  simp only [CollatzResearch.WordTrace]
  refine ⟨23606800411660077088148285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62951467764426872235062093 23606800411660077088148285)
  ·
    refine ⟨8852550154372528908055607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23606800411660077088148285 8852550154372528908055607)
    ·
      refine ⟨13278825231558793362083411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8852550154372528908055607 13278825231558793362083411)
      ·
        refine ⟨19918237847338190043125117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13278825231558793362083411 19918237847338190043125117)
        ·
          refine ⟨7469339192751821266171919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19918237847338190043125117 7469339192751821266171919)
          ·
            refine ⟨11204008789127731899257879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7469339192751821266171919 11204008789127731899257879)
            ·
              refine ⟨16806013183691597848886819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11204008789127731899257879 16806013183691597848886819)
              ·
                refine ⟨25209019775537396773330229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16806013183691597848886819 25209019775537396773330229)
                ·
                  refine ⟨2363345603956630947499709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25209019775537396773330229 2363345603956630947499709)
                  ·
                    refine ⟨886254601483736605312391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2363345603956630947499709 886254601483736605312391)
                    ·
                      rfl

theorem cell22_2588962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_2588962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2588962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2588962 prefixEnd_2588962 := by exact prefixLift 2588962
  have htrace : WordTrace (prefixWord ++ tailWord_2588962) baseStart_2588962 baseEnd_2588962 := by
    simpa [prefixWord, tailWord_2588962, baseEnd_2588962] using wordTrace_append hprefix tailTrace_2588962
  have hstable : (prefixWord ++ tailWord_2588962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588962).length < 2 ^ (prefixWord ++ tailWord_2588962).sum := by decide
  have hdescent : baseEnd_2588962 < baseStart_2588962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588979 : List Nat := [1, 1, 1, 2, 5, 1, 4, 3, 1, 3]
def baseStart_2588979 : Nat := 118140960795 + 2588979 * 2 ^ 59
def prefixEnd_2588979 : Nat := 4983230072969 + 3 ^ 40 * 2588979 * 2
def baseEnd_2588979 : Nat := 886260420931154227637339

theorem tailTrace_2588979 : CollatzResearch.WordTrace tailWord_2588979 prefixEnd_2588979 886260420931154227637339 := by
  unfold tailWord_2588979
  simp only [CollatzResearch.WordTrace]
  refine ⟨94427821687578720255961991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62951881125052480170641327 94427821687578720255961991)
  ·
    refine ⟨141641732531368080383942987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94427821687578720255961991 141641732531368080383942987)
    ·
      refine ⟨212462598797052120575914481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141641732531368080383942987 212462598797052120575914481)
      ·
        refine ⟨159346949097789090431935861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212462598797052120575914481 159346949097789090431935861)
        ·
          refine ⟨14938776477917727227993987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 159346949097789090431935861 14938776477917727227993987)
          ·
            refine ⟨22408164716876590841990981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14938776477917727227993987 22408164716876590841990981)
            ·
              refine ⟨4201530884414360782873309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22408164716876590841990981 4201530884414360782873309)
              ·
                refine ⟨1575574081655385293577491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4201530884414360782873309 1575574081655385293577491)
                ·
                  refine ⟨2363361122483077940366237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1575574081655385293577491 2363361122483077940366237)
                  ·
                    refine ⟨886260420931154227637339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2363361122483077940366237 886260420931154227637339)
                    ·
                      rfl

theorem cell22_2588979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 3, 1, 3].length) (baseStart_2588979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2588979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2588979 prefixEnd_2588979 := by exact prefixLift 2588979
  have htrace : WordTrace (prefixWord ++ tailWord_2588979) baseStart_2588979 baseEnd_2588979 := by
    simpa [prefixWord, tailWord_2588979, baseEnd_2588979] using wordTrace_append hprefix tailTrace_2588979
  have hstable : (prefixWord ++ tailWord_2588979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588979).length < 2 ^ (prefixWord ++ tailWord_2588979).sum := by decide
  have hdescent : baseEnd_2588979 < baseStart_2588979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588996 : List Nat := [2, 3, 4, 1, 2, 1, 2, 1, 3, 3]
def baseStart_2588996 : Nat := 118140960795 + 2588996 * 2 ^ 59
def prefixEnd_2588996 : Nat := 4983230072969 + 3 ^ 40 * 2588996 * 2
def baseEnd_2588996 : Nat := 886266240378571849962287

theorem tailTrace_2588996 : CollatzResearch.WordTrace tailWord_2588996 prefixEnd_2588996 886266240378571849962287 := by
  unfold tailWord_2588996
  simp only [CollatzResearch.WordTrace]
  refine ⟨47214220864258566079665421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62952294485678088106220561 47214220864258566079665421)
  ·
    refine ⟨17705332824096962279874533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47214220864258566079665421 17705332824096962279874533)
    ·
      refine ⟨3319749904518180427476475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17705332824096962279874533 3319749904518180427476475)
      ·
        refine ⟨4979624856777270641214713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3319749904518180427476475 4979624856777270641214713)
        ·
          refine ⟨3734718642582952980911035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4979624856777270641214713 3734718642582952980911035)
          ·
            refine ⟨5602077963874429471366553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3734718642582952980911035 5602077963874429471366553)
            ·
              refine ⟨4201558472905822103524915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5602077963874429471366553 4201558472905822103524915)
              ·
                refine ⟨6302337709358733155287373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4201558472905822103524915 6302337709358733155287373)
                ·
                  refine ⟨2363376641009524933232765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6302337709358733155287373 2363376641009524933232765)
                  ·
                    refine ⟨886266240378571849962287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2363376641009524933232765 886266240378571849962287)
                    ·
                      rfl

theorem cell22_2588996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_2588996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2588996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2588996 prefixEnd_2588996 := by exact prefixLift 2588996
  have htrace : WordTrace (prefixWord ++ tailWord_2588996) baseStart_2588996 baseEnd_2588996 := by
    simpa [prefixWord, tailWord_2588996, baseEnd_2588996] using wordTrace_append hprefix tailTrace_2588996
  have hstable : (prefixWord ++ tailWord_2588996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588996).length < 2 ^ (prefixWord ++ tailWord_2588996).sum := by decide
  have hdescent : baseEnd_2588996 < baseStart_2588996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589065 : List Nat := [1, 2, 1, 1, 6, 1, 1, 9]
def baseStart_2589065 : Nat := 118140960795 + 2589065 * 2 ^ 59
def prefixEnd_2589065 : Nat := 4983230072969 + 3 ^ 40 * 2589065 * 2
def baseEnd_2589065 : Nat := 98476651165408741109675

theorem tailTrace_2589065 : CollatzResearch.WordTrace tailWord_2589065 prefixEnd_2589065 98476651165408741109675 := by
  unfold tailWord_2589065
  simp only [CollatzResearch.WordTrace]
  refine ⟨94430958365267156943592649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62953972243511437962395099 94430958365267156943592649)
  ·
    refine ⟨70823218773950367707694487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94430958365267156943592649 70823218773950367707694487)
    ·
      refine ⟨106234828160925551561541731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70823218773950367707694487 106234828160925551561541731)
      ·
        refine ⟨159352242241388327342312597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106234828160925551561541731 159352242241388327342312597)
        ·
          refine ⟨7469636355065077844170903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 159352242241388327342312597 7469636355065077844170903)
          ·
            refine ⟨11204454532597616766256355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7469636355065077844170903 11204454532597616766256355)
            ·
              refine ⟨16806681798896425149384533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11204454532597616766256355 16806681798896425149384533)
              ·
                refine ⟨98476651165408741109675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16806681798896425149384533 98476651165408741109675)
                ·
                  rfl

theorem cell22_2589065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 9].length) (baseStart_2589065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2589065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2589065 prefixEnd_2589065 := by exact prefixLift 2589065
  have htrace : WordTrace (prefixWord ++ tailWord_2589065) baseStart_2589065 baseEnd_2589065 := by
    simpa [prefixWord, tailWord_2589065, baseEnd_2589065] using wordTrace_append hprefix tailTrace_2589065
  have hstable : (prefixWord ++ tailWord_2589065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589065).length < 2 ^ (prefixWord ++ tailWord_2589065).sum := by decide
  have hdescent : baseEnd_2589065 < baseStart_2589065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589127 : List Nat := [1, 1, 4, 1, 1, 4, 2, 3, 5]
def baseStart_2589127 : Nat := 118140960795 + 2589127 * 2 ^ 59
def prefixEnd_2589127 : Nat := 4983230072969 + 3 ^ 40 * 2589127 * 2
def baseEnd_2589127 : Nat := 295437028118577058312295

theorem tailTrace_2589127 : CollatzResearch.WordTrace tailWord_2589127 prefixEnd_2589127 295437028118577058312295 := by
  unfold tailWord_2589127
  simp only [CollatzResearch.WordTrace]
  refine ⟨94433219691042541532349635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62955479794028361021566423 94433219691042541532349635)
  ·
    refine ⟨141649829536563812298524453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94433219691042541532349635 141649829536563812298524453)
    ·
      refine ⟨26559343038105714805973335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141649829536563812298524453 26559343038105714805973335)
      ·
        refine ⟨39839014557158572208960003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26559343038105714805973335 39839014557158572208960003)
        ·
          refine ⟨59758521835737858313440005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39839014557158572208960003 59758521835737858313440005)
          ·
            refine ⟨11204722844200848433770001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59758521835737858313440005 11204722844200848433770001)
            ·
              refine ⟨8403542133150636325327501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11204722844200848433770001 8403542133150636325327501)
              ·
                refine ⟨3151328299931488621997813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8403542133150636325327501 3151328299931488621997813)
                ·
                  refine ⟨295437028118577058312295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3151328299931488621997813 295437028118577058312295)
                  ·
                    rfl

theorem cell22_2589127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 3, 5].length) (baseStart_2589127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2589127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2589127 prefixEnd_2589127 := by exact prefixLift 2589127
  have htrace : WordTrace (prefixWord ++ tailWord_2589127) baseStart_2589127 baseEnd_2589127 := by
    simpa [prefixWord, tailWord_2589127, baseEnd_2589127] using wordTrace_append hprefix tailTrace_2589127
  have hstable : (prefixWord ++ tailWord_2589127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589127).length < 2 ^ (prefixWord ++ tailWord_2589127).sum := by decide
  have hdescent : baseEnd_2589127 < baseStart_2589127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589191 : List Nat := [1, 1, 4, 3, 3, 1, 2, 2, 1, 4]
def baseStart_2589191 : Nat := 118140960795 + 2589191 * 2 ^ 59
def prefixEnd_2589191 : Nat := 4983230072969 + 3 ^ 40 * 2589191 * 2
def baseEnd_2589191 : Nat := 886332992863656341336689

theorem tailTrace_2589191 : CollatzResearch.WordTrace tailWord_2589191 prefixEnd_2589191 886332992863656341336689 := by
  unfold tailWord_2589191
  simp only [CollatzResearch.WordTrace]
  refine ⟨94435553962810680462679427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62957035975207120308452951 94435553962810680462679427)
  ·
    refine ⟨141653330944216020694019141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94435553962810680462679427 141653330944216020694019141)
    ·
      refine ⟨26559999552040503880128589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141653330944216020694019141 26559999552040503880128589)
      ·
        refine ⟨9959999832015188955048221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26559999552040503880128589 9959999832015188955048221)
        ·
          refine ⟨3734999937005695858143083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9959999832015188955048221 3734999937005695858143083)
          ·
            refine ⟨5602499905508543787214625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3734999937005695858143083 5602499905508543787214625)
            ·
              refine ⟨4201874929131407840410969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5602499905508543787214625 4201874929131407840410969)
              ·
                refine ⟨3151406196848555880308227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4201874929131407840410969 3151406196848555880308227)
                ·
                  refine ⟨4727109295272833820462341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3151406196848555880308227 4727109295272833820462341)
                  ·
                    refine ⟨886332992863656341336689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4727109295272833820462341 886332992863656341336689)
                    ·
                      rfl

theorem cell22_2589191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_2589191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2589191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2589191 prefixEnd_2589191 := by exact prefixLift 2589191
  have htrace : WordTrace (prefixWord ++ tailWord_2589191) baseStart_2589191 baseEnd_2589191 := by
    simpa [prefixWord, tailWord_2589191, baseEnd_2589191] using wordTrace_append hprefix tailTrace_2589191
  have hstable : (prefixWord ++ tailWord_2589191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589191).length < 2 ^ (prefixWord ++ tailWord_2589191).sum := by decide
  have hdescent : baseEnd_2589191 < baseStart_2589191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589219 : List Nat := [1, 1, 1, 4, 4, 2, 1, 2, 2, 4]
def baseStart_2589219 : Nat := 118140960795 + 2589219 * 2 ^ 59
def prefixEnd_2589219 : Nat := 4983230072969 + 3 ^ 40 * 2589219 * 2
def baseEnd_2589219 : Nat := 886342577835873601636603

theorem tailTrace_2589219 : CollatzResearch.WordTrace tailWord_2589219 prefixEnd_2589219 886342577835873601636603 := by
  unfold tailWord_2589219
  simp only [CollatzResearch.WordTrace]
  refine ⟨94436575206709241244698711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62957716804472827496465807 94436575206709241244698711)
  ·
    refine ⟨141654862810063861867048067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94436575206709241244698711 141654862810063861867048067)
    ·
      refine ⟨212482294215095792800572101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141654862810063861867048067 212482294215095792800572101)
      ·
        refine ⟨39840430165330461150107269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 212482294215095792800572101 39840430165330461150107269)
        ·
          refine ⟨7470080655999461465645113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39840430165330461150107269 7470080655999461465645113)
          ·
            refine ⟨5602560491999596099233835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7470080655999461465645113 5602560491999596099233835)
            ·
              refine ⟨8403840737999394148850753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5602560491999596099233835 8403840737999394148850753)
              ·
                refine ⟨6302880553499545611638065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8403840737999394148850753 6302880553499545611638065)
                ·
                  refine ⟨4727160415124659208728549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6302880553499545611638065 4727160415124659208728549)
                  ·
                    refine ⟨886342577835873601636603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4727160415124659208728549 886342577835873601636603)
                    ·
                      rfl

theorem cell22_2589219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 2, 4].length) (baseStart_2589219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2589219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2589219 prefixEnd_2589219 := by exact prefixLift 2589219
  have htrace : WordTrace (prefixWord ++ tailWord_2589219) baseStart_2589219 baseEnd_2589219 := by
    simpa [prefixWord, tailWord_2589219, baseEnd_2589219] using wordTrace_append hprefix tailTrace_2589219
  have hstable : (prefixWord ++ tailWord_2589219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589219).length < 2 ^ (prefixWord ++ tailWord_2589219).sum := by decide
  have hdescent : baseEnd_2589219 < baseStart_2589219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589223 : List Nat := [1, 1, 7, 2, 1, 2, 1, 1, 6]
def baseStart_2589223 : Nat := 118140960795 + 2589223 * 2 ^ 59
def prefixEnd_2589223 : Nat := 4983230072969 + 3 ^ 40 * 2589223 * 2
def baseEnd_2589223 : Nat := 295447982372539641512197

theorem tailTrace_2589223 : CollatzResearch.WordTrace tailWord_2589223 prefixEnd_2589223 295447982372539641512197 := by
  unfold tailWord_2589223
  simp only [CollatzResearch.WordTrace]
  refine ⟨94436721098694749927844323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62957814065796499951896215 94436721098694749927844323)
  ·
    refine ⟨141655081648042124891766485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94436721098694749927844323 141655081648042124891766485)
    ·
      refine ⟨3320040976125987302150777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 141655081648042124891766485 3320040976125987302150777)
      ·
        refine ⟨2490030732094490476613083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3320040976125987302150777 2490030732094490476613083)
        ·
          refine ⟨3735046098141735714919625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2490030732094490476613083 3735046098141735714919625)
          ·
            refine ⟨2801284573606301786189719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3735046098141735714919625 2801284573606301786189719)
            ·
              refine ⟨4201926860409452679284579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2801284573606301786189719 4201926860409452679284579)
              ·
                refine ⟨6302890290614179018926869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4201926860409452679284579 6302890290614179018926869)
                ·
                  refine ⟨295447982372539641512197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6302890290614179018926869 295447982372539641512197)
                  ·
                    rfl

theorem cell22_2589223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 6].length) (baseStart_2589223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2589223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2589223 prefixEnd_2589223 := by exact prefixLift 2589223
  have htrace : WordTrace (prefixWord ++ tailWord_2589223) baseStart_2589223 baseEnd_2589223 := by
    simpa [prefixWord, tailWord_2589223, baseEnd_2589223] using wordTrace_append hprefix tailTrace_2589223
  have hstable : (prefixWord ++ tailWord_2589223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589223).length < 2 ^ (prefixWord ++ tailWord_2589223).sum := by decide
  have hdescent : baseEnd_2589223 < baseStart_2589223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589238 : List Nat := [5, 1, 2, 1, 2, 2, 1, 3, 2, 3]
def baseStart_2589238 : Nat := 118140960795 + 2589238 * 2 ^ 59
def prefixEnd_2589238 : Nat := 4983230072969 + 3 ^ 40 * 2589238 * 2
def baseEnd_2589238 : Nat := 886349081924163885411545

theorem tailTrace_2589238 : CollatzResearch.WordTrace tailWord_2589238 prefixEnd_2589238 886349081924163885411545 := by
  unfold tailWord_2589238
  simp only [CollatzResearch.WordTrace]
  refine ⟨5902329262102525468102523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62958178795760271659760245 5902329262102525468102523)
  ·
    refine ⟨8853493893153788202153785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5902329262102525468102523 8853493893153788202153785)
    ·
      refine ⟨6640120419865341151615339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8853493893153788202153785 6640120419865341151615339)
      ·
        refine ⟨9960180629798011727423009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6640120419865341151615339 9960180629798011727423009)
        ·
          refine ⟨7470135472348508795567257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9960180629798011727423009 7470135472348508795567257)
          ·
            refine ⟨5602601604261381596675443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7470135472348508795567257 5602601604261381596675443)
            ·
              refine ⟨8403902406392072395013165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5602601604261381596675443 8403902406392072395013165)
              ·
                refine ⟨3151463402397027148129937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8403902406392072395013165 3151463402397027148129937)
                ·
                  refine ⟨2363597551797770361097453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3151463402397027148129937 2363597551797770361097453)
                  ·
                    refine ⟨886349081924163885411545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2363597551797770361097453 886349081924163885411545)
                    ·
                      rfl

theorem cell22_2589238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_2589238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2589238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2589238 prefixEnd_2589238 := by exact prefixLift 2589238
  have htrace : WordTrace (prefixWord ++ tailWord_2589238) baseStart_2589238 baseEnd_2589238 := by
    simpa [prefixWord, tailWord_2589238, baseEnd_2589238] using wordTrace_append hprefix tailTrace_2589238
  have hstable : (prefixWord ++ tailWord_2589238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589238).length < 2 ^ (prefixWord ++ tailWord_2589238).sum := by decide
  have hdescent : baseEnd_2589238 < baseStart_2589238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589262 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 9]
def baseStart_2589262 : Nat := 118140960795 + 2589262 * 2 ^ 59
def prefixEnd_2589262 : Nat := 4983230072969 + 3 ^ 40 * 2589262 * 2
def baseEnd_2589262 : Nat := 295452432538211940937157

theorem tailTrace_2589262 : CollatzResearch.WordTrace tailWord_2589262 prefixEnd_2589262 295452432538211940937157 := by
  unfold tailWord_2589262
  simp only [CollatzResearch.WordTrace]
  refine ⟨11804767943194182448564255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62958762363702306392342693 11804767943194182448564255)
  ·
    refine ⟨17707151914791273672846383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11804767943194182448564255 17707151914791273672846383)
    ·
      refine ⟨26560727872186910509269575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17707151914791273672846383 26560727872186910509269575)
      ·
        refine ⟨39841091808280365763904363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26560727872186910509269575 39841091808280365763904363)
        ·
          refine ⟨59761637712420548645856545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39841091808280365763904363 59761637712420548645856545)
          ·
            refine ⟨44821228284315411484392409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59761637712420548645856545 44821228284315411484392409)
            ·
              refine ⟨33615921213236558613294307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44821228284315411484392409 33615921213236558613294307)
              ·
                refine ⟨50423881819854837919941461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33615921213236558613294307 50423881819854837919941461)
                ·
                  refine ⟨295452432538211940937157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 50423881819854837919941461 295452432538211940937157)
                  ·
                    rfl

theorem cell22_2589262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_2589262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2589262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2589262 prefixEnd_2589262 := by exact prefixLift 2589262
  have htrace : WordTrace (prefixWord ++ tailWord_2589262) baseStart_2589262 baseEnd_2589262 := by
    simpa [prefixWord, tailWord_2589262, baseEnd_2589262] using wordTrace_append hprefix tailTrace_2589262
  have hstable : (prefixWord ++ tailWord_2589262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589262).length < 2 ^ (prefixWord ++ tailWord_2589262).sum := by decide
  have hdescent : baseEnd_2589262 < baseStart_2589262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589294 : List Nat := [4, 1, 2, 2, 2, 1, 1, 1, 1, 7]
def baseStart_2589294 : Nat := 118140960795 + 2589294 * 2 ^ 59
def prefixEnd_2589294 : Nat := 4983230072969 + 3 ^ 40 * 2589294 * 2
def baseEnd_2589294 : Nat := 886368251868598406011373

theorem tailTrace_2589294 : CollatzResearch.WordTrace tailWord_2589294 prefixEnd_2589294 886368251868598406011373 := by
  unfold tailWord_2589294
  simp only [CollatzResearch.WordTrace]
  refine ⟨11804913835179691131709867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62959540454291686035785957 11804913835179691131709867)
  ·
    refine ⟨17707370752769536697564801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11804913835179691131709867 17707370752769536697564801)
    ·
      refine ⟨13280528064577152523173601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17707370752769536697564801 13280528064577152523173601)
      ·
        refine ⟨9960396048432864392380201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13280528064577152523173601 9960396048432864392380201)
        ·
          refine ⟨7470297036324648294285151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9960396048432864392380201 7470297036324648294285151)
          ·
            refine ⟨11205445554486972441427727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7470297036324648294285151 11205445554486972441427727)
            ·
              refine ⟨16808168331730458662141591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11205445554486972441427727 16808168331730458662141591)
              ·
                refine ⟨25212252497595687993212387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16808168331730458662141591 25212252497595687993212387)
                ·
                  refine ⟨37818378746393531989818581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25212252497595687993212387 37818378746393531989818581)
                  ·
                    refine ⟨886368251868598406011373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37818378746393531989818581 886368251868598406011373)
                    ·
                      rfl

theorem cell22_2589294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_2589294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2589294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2589294 prefixEnd_2589294 := by exact prefixLift 2589294
  have htrace : WordTrace (prefixWord ++ tailWord_2589294) baseStart_2589294 baseEnd_2589294 := by
    simpa [prefixWord, tailWord_2589294, baseEnd_2589294] using wordTrace_append hprefix tailTrace_2589294
  have hstable : (prefixWord ++ tailWord_2589294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589294).length < 2 ^ (prefixWord ++ tailWord_2589294).sum := by decide
  have hdescent : baseEnd_2589294 < baseStart_2589294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589326 : List Nat := [4, 1, 1, 3, 1, 1, 3, 3, 1, 4]
def baseStart_2589326 : Nat := 118140960795 + 2589326 * 2 ^ 59
def prefixEnd_2589326 : Nat := 4983230072969 + 3 ^ 40 * 2589326 * 2
def baseEnd_2589326 : Nat := 886379206122560989211275

theorem tailTrace_2589326 : CollatzResearch.WordTrace tailWord_2589326 prefixEnd_2589326 886379206122560989211275 := by
  unfold tailWord_2589326
  simp only [CollatzResearch.WordTrace]
  refine ⟨11805059727165199814855479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62960318544881065679229221 11805059727165199814855479)
  ·
    refine ⟨17707589590747799722283219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11805059727165199814855479 17707589590747799722283219)
    ·
      refine ⟨26561384386121699583424829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17707589590747799722283219 26561384386121699583424829)
      ·
        refine ⟨9960519144795637343784311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26561384386121699583424829 9960519144795637343784311)
        ·
          refine ⟨14940778717193456015676467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9960519144795637343784311 14940778717193456015676467)
          ·
            refine ⟨22411168075790184023514701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14940778717193456015676467 22411168075790184023514701)
            ·
              refine ⟨8404188028421319008818013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22411168075790184023514701 8404188028421319008818013)
              ·
                refine ⟨3151570510657994628306755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8404188028421319008818013 3151570510657994628306755)
                ·
                  refine ⟨4727355765986991942460133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3151570510657994628306755 4727355765986991942460133)
                  ·
                    refine ⟨886379206122560989211275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4727355765986991942460133 886379206122560989211275)
                    ·
                      rfl

theorem cell22_2589326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_2589326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2589326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2589326 prefixEnd_2589326 := by exact prefixLift 2589326
  have htrace : WordTrace (prefixWord ++ tailWord_2589326) baseStart_2589326 baseEnd_2589326 := by
    simpa [prefixWord, tailWord_2589326, baseEnd_2589326] using wordTrace_append hprefix tailTrace_2589326
  have hstable : (prefixWord ++ tailWord_2589326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589326).length < 2 ^ (prefixWord ++ tailWord_2589326).sum := by decide
  have hdescent : baseEnd_2589326 < baseStart_2589326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589341 : List Nat := [1, 4, 2, 1, 1, 1, 4, 4, 4]
def baseStart_2589341 : Nat := 118140960795 + 2589341 * 2 ^ 59
def prefixEnd_2589341 : Nat := 4983230072969 + 3 ^ 40 * 2589341 * 2
def baseEnd_2589341 : Nat := 295461446976368650028743

theorem tailTrace_2589341 : CollatzResearch.WordTrace tailWord_2589341 prefixEnd_2589341 295461446976368650028743 := by
  unfold tailWord_2589341
  simp only [CollatzResearch.WordTrace]
  refine ⟨94441024912267256080639877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62960683274844837387093251 94441024912267256080639877)
  ·
    refine ⟨17707692171050110515119977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94441024912267256080639877 17707692171050110515119977)
    ·
      refine ⟨13280769128287582886339983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17707692171050110515119977 13280769128287582886339983)
      ·
        refine ⟨19921153692431374329509975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13280769128287582886339983 19921153692431374329509975)
        ·
          refine ⟨29881730538647061494264963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19921153692431374329509975 29881730538647061494264963)
          ·
            refine ⟨44822595807970592241397445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29881730538647061494264963 44822595807970592241397445)
            ·
              refine ⟨8404236713994486045262021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44822595807970592241397445 8404236713994486045262021)
              ·
                refine ⟨1575794383873966133486629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8404236713994486045262021 1575794383873966133486629)
                ·
                  refine ⟨295461446976368650028743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1575794383873966133486629 295461446976368650028743)
                  ·
                    rfl

theorem cell22_2589341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 4, 4].length) (baseStart_2589341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2589341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2589341 prefixEnd_2589341 := by exact prefixLift 2589341
  have htrace : WordTrace (prefixWord ++ tailWord_2589341) baseStart_2589341 baseEnd_2589341 := by
    simpa [prefixWord, tailWord_2589341, baseEnd_2589341] using wordTrace_append hprefix tailTrace_2589341
  have hstable : (prefixWord ++ tailWord_2589341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589341).length < 2 ^ (prefixWord ++ tailWord_2589341).sum := by decide
  have hdescent : baseEnd_2589341 < baseStart_2589341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589459 : List Nat := [1, 1, 1, 2, 1, 3, 4, 3, 6]
def baseStart_2589459 : Nat := 118140960795 + 2589459 * 2 ^ 59
def prefixEnd_2589459 : Nat := 4983230072969 + 3 ^ 40 * 2589459 * 2
def baseEnd_2589459 : Nat := 295474911580197658545289

theorem tailTrace_2589459 : CollatzResearch.WordTrace tailWord_2589459 prefixEnd_2589459 295474911580197658545289 := by
  unfold tailWord_2589459
  simp only [CollatzResearch.WordTrace]
  refine ⟨94445328725839762233435431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62963552483893174822290287 94445328725839762233435431)
  ·
    refine ⟨141667993088759643350153147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94445328725839762233435431 141667993088759643350153147)
    ·
      refine ⟨212501989633139465025229721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141667993088759643350153147 212501989633139465025229721)
      ·
        refine ⟨159376492224854598768922291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212501989633139465025229721 159376492224854598768922291)
        ·
          refine ⟨239064738337281898153383437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159376492224854598768922291 239064738337281898153383437)
          ·
            refine ⟨89649276876480711807518789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 239064738337281898153383437 89649276876480711807518789)
            ·
              refine ⟨16809239414340133463909773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89649276876480711807518789 16809239414340133463909773)
              ·
                refine ⟨6303464780377550048966165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16809239414340133463909773 6303464780377550048966165)
                ·
                  refine ⟨295474911580197658545289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6303464780377550048966165 295474911580197658545289)
                  ·
                    rfl

theorem cell22_2589459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 6].length) (baseStart_2589459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2589459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2589459 prefixEnd_2589459 := by exact prefixLift 2589459
  have htrace : WordTrace (prefixWord ++ tailWord_2589459) baseStart_2589459 baseEnd_2589459 := by
    simpa [prefixWord, tailWord_2589459, baseEnd_2589459] using wordTrace_append hprefix tailTrace_2589459
  have hstable : (prefixWord ++ tailWord_2589459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589459).length < 2 ^ (prefixWord ++ tailWord_2589459).sum := by decide
  have hdescent : baseEnd_2589459 < baseStart_2589459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589491 : List Nat := [1, 1, 1, 2, 6, 1, 2, 2, 1, 5]
def baseStart_2589491 : Nat := 118140960795 + 2589491 * 2 ^ 59
def prefixEnd_2589491 : Nat := 4983230072969 + 3 ^ 40 * 2589491 * 2
def baseEnd_2589491 : Nat := 886435688994555558835769

theorem tailTrace_2589491 : CollatzResearch.WordTrace tailWord_2589491 prefixEnd_2589491 886435688994555558835769 := by
  unfold tailWord_2589491
  simp only [CollatzResearch.WordTrace]
  refine ⟨94446495861723831698600327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62964330574482554465733551 94446495861723831698600327)
  ·
    refine ⟨141669743792585747547900491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94446495861723831698600327 141669743792585747547900491)
    ·
      refine ⟨212504615688878621321850737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141669743792585747547900491 212504615688878621321850737)
      ·
        refine ⟨159378461766658965991388053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212504615688878621321850737 159378461766658965991388053)
        ·
          refine ⟨7470865395312139030846315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 159378461766658965991388053 7470865395312139030846315)
          ·
            refine ⟨11206298092968208546269473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7470865395312139030846315 11206298092968208546269473)
            ·
              refine ⟨8404723569726156409702105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11206298092968208546269473 8404723569726156409702105)
              ·
                refine ⟨6303542677294617307276579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8404723569726156409702105 6303542677294617307276579)
                ·
                  refine ⟨9455314015941925960914869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6303542677294617307276579 9455314015941925960914869)
                  ·
                    refine ⟨886435688994555558835769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9455314015941925960914869 886435688994555558835769)
                    ·
                      rfl

theorem cell22_2589491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 5].length) (baseStart_2589491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2589491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2589491 prefixEnd_2589491 := by exact prefixLift 2589491
  have htrace : WordTrace (prefixWord ++ tailWord_2589491) baseStart_2589491 baseEnd_2589491 := by
    simpa [prefixWord, tailWord_2589491, baseEnd_2589491] using wordTrace_append hprefix tailTrace_2589491
  have hstable : (prefixWord ++ tailWord_2589491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589491).length < 2 ^ (prefixWord ++ tailWord_2589491).sum := by decide
  have hdescent : baseEnd_2589491 < baseStart_2589491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589493 : List Nat := [1, 3, 3, 1, 3, 1, 1, 5, 4]
def baseStart_2589493 : Nat := 118140960795 + 2589493 * 2 ^ 59
def prefixEnd_2589493 : Nat := 4983230072969 + 3 ^ 40 * 2589493 * 2
def baseEnd_2589493 : Nat := 295478791211809406761921

theorem tailTrace_2589493 : CollatzResearch.WordTrace tailWord_2589493 prefixEnd_2589493 295478791211809406761921 := by
  unfold tailWord_2589493
  simp only [CollatzResearch.WordTrace]
  refine ⟨94446568807716586040173133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62964379205144390693448755 94446568807716586040173133)
  ·
    refine ⟨35417463302893719765064925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94446568807716586040173133 35417463302893719765064925)
    ·
      refine ⟨13281548738585144911899347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35417463302893719765064925 13281548738585144911899347)
      ·
        refine ⟨19922323107877717367849021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13281548738585144911899347 19922323107877717367849021)
        ·
          refine ⟨7470871165454144012943383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19922323107877717367849021 7470871165454144012943383)
          ·
            refine ⟨11206306748181216019415075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7470871165454144012943383 11206306748181216019415075)
            ·
              refine ⟨16809460122271824029122613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11206306748181216019415075 16809460122271824029122613)
              ·
                refine ⟨1575886886462983502730245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16809460122271824029122613 1575886886462983502730245)
                ·
                  refine ⟨295478791211809406761921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1575886886462983502730245 295478791211809406761921)
                  ·
                    rfl

theorem cell22_2589493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 5, 4].length) (baseStart_2589493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2589493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2589493 prefixEnd_2589493 := by exact prefixLift 2589493
  have htrace : WordTrace (prefixWord ++ tailWord_2589493) baseStart_2589493 baseEnd_2589493 := by
    simpa [prefixWord, tailWord_2589493, baseEnd_2589493] using wordTrace_append hprefix tailTrace_2589493
  have hstable : (prefixWord ++ tailWord_2589493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589493).length < 2 ^ (prefixWord ++ tailWord_2589493).sum := by decide
  have hdescent : baseEnd_2589493 < baseStart_2589493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589525 : List Nat := [1, 3, 2, 2, 2, 1, 5, 1, 2, 3]
def baseStart_2589525 : Nat := 118140960795 + 2589525 * 2 ^ 59
def prefixEnd_2589525 : Nat := 4983230072969 + 3 ^ 40 * 2589525 * 2
def baseEnd_2589525 : Nat := 886447327889390803485665

theorem tailTrace_2589525 : CollatzResearch.WordTrace tailWord_2589525 prefixEnd_2589525 886447327889390803485665 := by
  unfold tailWord_2589525
  simp only [CollatzResearch.WordTrace]
  refine ⟨94447735943600655505338029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62965157295733770336892019 94447735943600655505338029)
  ·
    refine ⟨35417900978850245814501761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94447735943600655505338029 35417900978850245814501761)
    ·
      refine ⟨26563425734137684360876321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35417900978850245814501761 26563425734137684360876321)
      ·
        refine ⟨19922569300603263270657241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26563425734137684360876321 19922569300603263270657241)
        ·
          refine ⟨14941926975452447452992931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19922569300603263270657241 14941926975452447452992931)
          ·
            refine ⟨22412890463178671179489397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14941926975452447452992931 22412890463178671179489397)
            ·
              refine ⟨2101208480923000423077131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22412890463178671179489397 2101208480923000423077131)
              ·
                refine ⟨3151812721384500634615697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2101208480923000423077131 3151812721384500634615697)
                ·
                  refine ⟨2363859541038375475961773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3151812721384500634615697 2363859541038375475961773)
                  ·
                    refine ⟨886447327889390803485665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2363859541038375475961773 886447327889390803485665)
                    ·
                      rfl

theorem cell22_2589525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 1, 2, 3].length) (baseStart_2589525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2589525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2589525 prefixEnd_2589525 := by exact prefixLift 2589525
  have htrace : WordTrace (prefixWord ++ tailWord_2589525) baseStart_2589525 baseEnd_2589525 := by
    simpa [prefixWord, tailWord_2589525, baseEnd_2589525] using wordTrace_append hprefix tailTrace_2589525
  have hstable : (prefixWord ++ tailWord_2589525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589525).length < 2 ^ (prefixWord ++ tailWord_2589525).sum := by decide
  have hdescent : baseEnd_2589525 < baseStart_2589525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589538 : List Nat := [3, 3, 2, 1, 3, 1, 1, 8]
def baseStart_2589538 : Nat := 118140960795 + 2589538 * 2 ^ 59
def prefixEnd_2589538 : Nat := 4983230072969 + 3 ^ 40 * 2589538 * 2
def baseEnd_2589538 : Nat := 98494642006118122545625

theorem tailTrace_2589538 : CollatzResearch.WordTrace tailWord_2589538 prefixEnd_2589538 98494642006118122545625 := by
  unfold tailWord_2589538
  simp only [CollatzResearch.WordTrace]
  refine ⟨23612052523138389681390317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62965473395035705817040845 23612052523138389681390317)
  ·
    refine ⟨8854519696176896130521369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23612052523138389681390317 8854519696176896130521369)
    ·
      refine ⟨6640889772132672097891027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8854519696176896130521369 6640889772132672097891027)
      ·
        refine ⟨9961334658199008146836541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6640889772132672097891027 9961334658199008146836541)
        ·
          refine ⟨3735500496824628055063703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9961334658199008146836541 3735500496824628055063703)
          ·
            refine ⟨5603250745236942082595555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3735500496824628055063703 5603250745236942082595555)
            ·
              refine ⟨8404876117855413123893333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5603250745236942082595555 8404876117855413123893333)
              ·
                refine ⟨98494642006118122545625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8404876117855413123893333 98494642006118122545625)
                ·
                  rfl

theorem cell22_2589538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 8].length) (baseStart_2589538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2589538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2589538 prefixEnd_2589538 := by exact prefixLift 2589538
  have htrace : WordTrace (prefixWord ++ tailWord_2589538) baseStart_2589538 baseEnd_2589538 := by
    simpa [prefixWord, tailWord_2589538, baseEnd_2589538] using wordTrace_append hprefix tailTrace_2589538
  have hstable : (prefixWord ++ tailWord_2589538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589538).length < 2 ^ (prefixWord ++ tailWord_2589538).sum := by decide
  have hdescent : baseEnd_2589538 < baseStart_2589538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589626 : List Nat := [3, 1, 1, 1, 2, 1, 3, 2, 3, 5]
def baseStart_2589626 : Nat := 118140960795 + 2589626 * 2 ^ 59
def prefixEnd_2589626 : Nat := 4983230072969 + 3 ^ 40 * 2589626 * 2
def baseEnd_2589626 : Nat := 886481902253460206710355

theorem tailTrace_2589626 : CollatzResearch.WordTrace tailWord_2589626 prefixEnd_2589626 886481902253460206710355 := by
  unfold tailWord_2589626
  simp only [CollatzResearch.WordTrace]
  refine ⟨23612854929058687438691183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62967613144156499836509821 23612854929058687438691183)
  ·
    refine ⟨35419282393588031158036775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23612854929058687438691183 35419282393588031158036775)
    ·
      refine ⟨53128923590382046737055163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35419282393588031158036775 53128923590382046737055163)
      ·
        refine ⟨79693385385573070105582745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53128923590382046737055163 79693385385573070105582745)
        ·
          refine ⟨59770039039179802579187059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79693385385573070105582745 59770039039179802579187059)
          ·
            refine ⟨89655058558769703868780589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59770039039179802579187059 89655058558769703868780589)
            ·
              refine ⟨33620646959538638950792721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89655058558769703868780589 33620646959538638950792721)
              ·
                refine ⟨25215485219653979213094541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33620646959538638950792721 25215485219653979213094541)
                ·
                  refine ⟨9455806957370242204910453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25215485219653979213094541 9455806957370242204910453)
                  ·
                    refine ⟨886481902253460206710355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9455806957370242204910453 886481902253460206710355)
                    ·
                      rfl

theorem cell22_2589626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_2589626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2589626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2589626 prefixEnd_2589626 := by exact prefixLift 2589626
  have htrace : WordTrace (prefixWord ++ tailWord_2589626) baseStart_2589626 baseEnd_2589626 := by
    simpa [prefixWord, tailWord_2589626, baseEnd_2589626] using wordTrace_append hprefix tailTrace_2589626
  have hstable : (prefixWord ++ tailWord_2589626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589626).length < 2 ^ (prefixWord ++ tailWord_2589626).sum := by decide
  have hdescent : baseEnd_2589626 < baseStart_2589626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589643 : List Nat := [1, 1, 1, 1, 3, 6, 2, 1, 1, 5]
def baseStart_2589643 : Nat := 118140960795 + 2589643 * 2 ^ 59
def prefixEnd_2589643 : Nat := 4983230072969 + 3 ^ 40 * 2589643 * 2
def baseEnd_2589643 : Nat := 886487721700877829035303

theorem tailTrace_2589643 : CollatzResearch.WordTrace tailWord_2589643 prefixEnd_2589643 886487721700877829035303 := by
  unfold tailWord_2589643
  simp only [CollatzResearch.WordTrace]
  refine ⟨94452039757173161658133583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62968026504782107772089055 94452039757173161658133583)
  ·
    refine ⟨141678059635759742487200375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94452039757173161658133583 141678059635759742487200375)
    ·
      refine ⟨212517089453639613730800563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141678059635759742487200375 212517089453639613730800563)
      ·
        refine ⟨318775634180459420596200845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212517089453639613730800563 318775634180459420596200845)
        ·
          refine ⟨119540862817672282723575317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 318775634180459420596200845 119540862817672282723575317)
          ·
            refine ⟨5603477944578388252667593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 119540862817672282723575317 5603477944578388252667593)
            ·
              refine ⟨4202608458433791189500695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5603477944578388252667593 4202608458433791189500695)
              ·
                refine ⟨6303912687650686784251043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4202608458433791189500695 6303912687650686784251043)
                ·
                  refine ⟨9455869031476030176376565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6303912687650686784251043 9455869031476030176376565)
                  ·
                    refine ⟨886487721700877829035303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9455869031476030176376565 886487721700877829035303)
                    ·
                      rfl

theorem cell22_2589643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 5].length) (baseStart_2589643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2589643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2589643 prefixEnd_2589643 := by exact prefixLift 2589643
  have htrace : WordTrace (prefixWord ++ tailWord_2589643) baseStart_2589643 baseEnd_2589643 := by
    simpa [prefixWord, tailWord_2589643, baseEnd_2589643] using wordTrace_append hprefix tailTrace_2589643
  have hstable : (prefixWord ++ tailWord_2589643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589643).length < 2 ^ (prefixWord ++ tailWord_2589643).sum := by decide
  have hdescent : baseEnd_2589643 < baseStart_2589643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589658 : List Nat := [3, 1, 1, 2, 4, 2, 1, 1, 1, 6]
def baseStart_2589658 : Nat := 118140960795 + 2589658 * 2 ^ 59
def prefixEnd_2589658 : Nat := 4983230072969 + 3 ^ 40 * 2589658 * 2
def baseEnd_2589658 : Nat := 886492856507422789910257

theorem tailTrace_2589658 : CollatzResearch.WordTrace tailWord_2589658 prefixEnd_2589658 886492856507422789910257 := by
  unfold tailWord_2589658
  simp only [CollatzResearch.WordTrace]
  refine ⟨23613146713029704804982407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62968391234745879479953085 23613146713029704804982407)
  ·
    refine ⟨35419720069544557207473611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23613146713029704804982407 35419720069544557207473611)
    ·
      refine ⟨53129580104316835811210417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35419720069544557207473611 53129580104316835811210417)
      ·
        refine ⟨39847185078237626858407813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53129580104316835811210417 39847185078237626858407813)
        ·
          refine ⟨7471347202169555035951465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39847185078237626858407813 7471347202169555035951465)
          ·
            refine ⟨5603510401627166276963599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7471347202169555035951465 5603510401627166276963599)
            ·
              refine ⟨8405265602440749415445399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5603510401627166276963599 8405265602440749415445399)
              ·
                refine ⟨12607898403661124123168099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8405265602440749415445399 12607898403661124123168099)
                ·
                  refine ⟨18911847605491686184752149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12607898403661124123168099 18911847605491686184752149)
                  ·
                    refine ⟨886492856507422789910257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18911847605491686184752149 886492856507422789910257)
                    ·
                      rfl

theorem cell22_2589658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 1, 6].length) (baseStart_2589658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2589658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2589658 prefixEnd_2589658 := by exact prefixLift 2589658
  have htrace : WordTrace (prefixWord ++ tailWord_2589658) baseStart_2589658 baseEnd_2589658 := by
    simpa [prefixWord, tailWord_2589658, baseEnd_2589658] using wordTrace_append hprefix tailTrace_2589658
  have hstable : (prefixWord ++ tailWord_2589658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589658).length < 2 ^ (prefixWord ++ tailWord_2589658).sum := by decide
  have hdescent : baseEnd_2589658 < baseStart_2589658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589694 : List Nat := [4, 2, 2, 2, 3, 1, 1, 1, 1, 5]
def baseStart_2589694 : Nat := 118140960795 + 2589694 * 2 ^ 59
def prefixEnd_2589694 : Nat := 4983230072969 + 3 ^ 40 * 2589694 * 2
def baseEnd_2589694 : Nat := 886505180043130696010147

theorem tailTrace_2589694 : CollatzResearch.WordTrace tailWord_2589694 prefixEnd_2589694 886505180043130696010147 := by
  unfold tailWord_2589694
  simp only [CollatzResearch.WordTrace]
  refine ⟨11806737484998549671030017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62969266586658931578826757 11806737484998549671030017)
  ·
    refine ⟨8855053113748912253272513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11806737484998549671030017 8855053113748912253272513)
    ·
      refine ⟨6641289835311684189954385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8855053113748912253272513 6641289835311684189954385)
      ·
        refine ⟨4980967376483763142465789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6641289835311684189954385 4980967376483763142465789)
        ·
          refine ⟨1867862766181411178424671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4980967376483763142465789 1867862766181411178424671)
          ·
            refine ⟨2801794149272116767637007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1867862766181411178424671 2801794149272116767637007)
            ·
              refine ⟨4202691223908175151455511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2801794149272116767637007 4202691223908175151455511)
              ·
                refine ⟨6304036835862262727183267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4202691223908175151455511 6304036835862262727183267)
                ·
                  refine ⟨9456055253793394090774901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6304036835862262727183267 9456055253793394090774901)
                  ·
                    refine ⟨886505180043130696010147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9456055253793394090774901 886505180043130696010147)
                    ·
                      rfl

theorem cell22_2589694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_2589694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2589694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2589694 prefixEnd_2589694 := by exact prefixLift 2589694
  have htrace : WordTrace (prefixWord ++ tailWord_2589694) baseStart_2589694 baseEnd_2589694 := by
    simpa [prefixWord, tailWord_2589694, baseEnd_2589694] using wordTrace_append hprefix tailTrace_2589694
  have hstable : (prefixWord ++ tailWord_2589694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589694).length < 2 ^ (prefixWord ++ tailWord_2589694).sum := by decide
  have hdescent : baseEnd_2589694 < baseStart_2589694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589735 : List Nat := [1, 1, 7, 1, 1, 1, 2, 1, 7]
def baseStart_2589735 : Nat := 118140960795 + 2589735 * 2 ^ 59
def prefixEnd_2589735 : Nat := 4983230072969 + 3 ^ 40 * 2589735 * 2
def baseEnd_2589735 : Nat := 295506405060340085245007

theorem tailTrace_2589735 : CollatzResearch.WordTrace tailWord_2589735 prefixEnd_2589735 295506405060340085245007 := by
  unfold tailWord_2589735
  simp only [CollatzResearch.WordTrace]
  refine ⟨94455395272839861370482659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62970263515226574246988439 94455395272839861370482659)
  ·
    refine ⟨141683092909259792055723989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94455395272839861370482659 141683092909259792055723989)
    ·
      refine ⟨3320697490060776376306031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 141683092909259792055723989 3320697490060776376306031)
      ·
        refine ⟨4981046235091164564459047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3320697490060776376306031 4981046235091164564459047)
        ·
          refine ⟨7471569352636746846688571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4981046235091164564459047 7471569352636746846688571)
          ·
            refine ⟨11207354028955120270032857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7471569352636746846688571 11207354028955120270032857)
            ·
              refine ⟨8405515521716340202524643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11207354028955120270032857 8405515521716340202524643)
              ·
                refine ⟨12608273282574510303786965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8405515521716340202524643 12608273282574510303786965)
                ·
                  refine ⟨295506405060340085245007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12608273282574510303786965 295506405060340085245007)
                  ·
                    rfl

theorem cell22_2589735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 7].length) (baseStart_2589735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2589735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2589735 prefixEnd_2589735 := by exact prefixLift 2589735
  have htrace : WordTrace (prefixWord ++ tailWord_2589735) baseStart_2589735 baseEnd_2589735 := by
    simpa [prefixWord, tailWord_2589735, baseEnd_2589735] using wordTrace_append hprefix tailTrace_2589735
  have hstable : (prefixWord ++ tailWord_2589735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589735).length < 2 ^ (prefixWord ++ tailWord_2589735).sum := by decide
  have hdescent : baseEnd_2589735 < baseStart_2589735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589752 : List Nat := [2, 1, 2, 1, 5, 3, 2, 1, 5]
def baseStart_2589752 : Nat := 118140960795 + 2589752 * 2 ^ 59
def prefixEnd_2589752 : Nat := 4983230072969 + 3 ^ 40 * 2589752 * 2
def baseEnd_2589752 : Nat := 295508344876145959353323

theorem tailTrace_2589752 : CollatzResearch.WordTrace tailWord_2589752 prefixEnd_2589752 295508344876145959353323 := by
  unfold tailWord_2589752
  simp only [CollatzResearch.WordTrace]
  refine ⟨47228007656889136636925755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62970676875852182182567673 47228007656889136636925755)
  ·
    refine ⟨70842011485333704955388633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47228007656889136636925755 70842011485333704955388633)
    ·
      refine ⟨53131508614000278716541475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70842011485333704955388633 53131508614000278716541475)
      ·
        refine ⟨79697262921000418074812213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53131508614000278716541475 79697262921000418074812213)
        ·
          refine ⟨7471618398843789194513645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79697262921000418074812213 7471618398843789194513645)
          ·
            refine ⟨2801856899566420947942617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7471618398843789194513645 2801856899566420947942617)
            ·
              refine ⟨2101392674674815710956963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2801856899566420947942617 2101392674674815710956963)
              ·
                refine ⟨3152089012012223566435445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2101392674674815710956963 3152089012012223566435445)
                ·
                  refine ⟨295508344876145959353323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3152089012012223566435445 295508344876145959353323)
                  ·
                    rfl

theorem cell22_2589752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 1, 5].length) (baseStart_2589752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2589752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2589752 prefixEnd_2589752 := by exact prefixLift 2589752
  have htrace : WordTrace (prefixWord ++ tailWord_2589752) baseStart_2589752 baseEnd_2589752 := by
    simpa [prefixWord, tailWord_2589752, baseEnd_2589752] using wordTrace_append hprefix tailTrace_2589752
  have hstable : (prefixWord ++ tailWord_2589752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589752).length < 2 ^ (prefixWord ++ tailWord_2589752).sum := by decide
  have hdescent : baseEnd_2589752 < baseStart_2589752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589765 : List Nat := [1, 3, 1, 1, 1, 3, 5, 2, 1, 4]
def baseStart_2589765 : Nat := 118140960795 + 2589765 * 2 ^ 59
def prefixEnd_2589765 : Nat := 4983230072969 + 3 ^ 40 * 2589765 * 2
def baseEnd_2589765 : Nat := 886529484794110177484929

theorem tailTrace_2589765 : CollatzResearch.WordTrace tailWord_2589765 prefixEnd_2589765 886529484794110177484929 := by
  unfold tailWord_2589765
  simp only [CollatzResearch.WordTrace]
  refine ⟨94456489462731176494074749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62970992975154117662716499 94456489462731176494074749)
  ·
    refine ⟨35421183548524191185278031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94456489462731176494074749 35421183548524191185278031)
    ·
      refine ⟨53131775322786286777917047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35421183548524191185278031 53131775322786286777917047)
      ·
        refine ⟨79697662984179430166875571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53131775322786286777917047 79697662984179430166875571)
        ·
          refine ⟨119546494476269145250313357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79697662984179430166875571 119546494476269145250313357)
          ·
            refine ⟨44829935428600929468867509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119546494476269145250313357 44829935428600929468867509)
            ·
              refine ⟨4202806446431337137706329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44829935428600929468867509 4202806446431337137706329)
              ·
                refine ⟨3152104834823502853279747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4202806446431337137706329 3152104834823502853279747)
                ·
                  refine ⟨4728157252235254279919621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3152104834823502853279747 4728157252235254279919621)
                  ·
                    refine ⟨886529484794110177484929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4728157252235254279919621 886529484794110177484929)
                    ·
                      rfl

theorem cell22_2589765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 2, 1, 4].length) (baseStart_2589765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2589765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2589765 prefixEnd_2589765 := by exact prefixLift 2589765
  have htrace : WordTrace (prefixWord ++ tailWord_2589765) baseStart_2589765 baseEnd_2589765 := by
    simpa [prefixWord, tailWord_2589765, baseEnd_2589765] using wordTrace_append hprefix tailTrace_2589765
  have hstable : (prefixWord ++ tailWord_2589765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589765).length < 2 ^ (prefixWord ++ tailWord_2589765).sum := by decide
  have hdescent : baseEnd_2589765 < baseStart_2589765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589790 : List Nat := [4, 4, 1, 1, 1, 3, 2, 2, 1, 3]
def baseStart_2589790 : Nat := 118140960795 + 2589790 * 2 ^ 59
def prefixEnd_2589790 : Nat := 4983230072969 + 3 ^ 40 * 2589790 * 2
def baseEnd_2589790 : Nat := 886538042805018445609853

theorem tailTrace_2589790 : CollatzResearch.WordTrace tailWord_2589790 prefixEnd_2589790 886538042805018445609853 := by
  unfold tailWord_2589790
  simp only [CollatzResearch.WordTrace]
  refine ⟨11807175160955075720466853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62971600858427070509156549 11807175160955075720466853)
  ·
    refine ⟨2213845342679076697587535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11807175160955075720466853 2213845342679076697587535)
    ·
      refine ⟨3320768014018615046381303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2213845342679076697587535 3320768014018615046381303)
      ·
        refine ⟨4981152021027922569571955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3320768014018615046381303 4981152021027922569571955)
        ·
          refine ⟨7471728031541883854357933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4981152021027922569571955 7471728031541883854357933)
          ·
            refine ⟨2801898011828206445384225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7471728031541883854357933 2801898011828206445384225)
            ·
              refine ⟨2101423508871154834038169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2801898011828206445384225 2101423508871154834038169)
              ·
                refine ⟨1576067631653366125528627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2101423508871154834038169 1576067631653366125528627)
                ·
                  refine ⟨2364101447480049188292941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1576067631653366125528627 2364101447480049188292941)
                  ·
                    refine ⟨886538042805018445609853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2364101447480049188292941 886538042805018445609853)
                    ·
                      rfl

theorem cell22_2589790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_2589790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2589790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2589790 prefixEnd_2589790 := by exact prefixLift 2589790
  have htrace : WordTrace (prefixWord ++ tailWord_2589790) baseStart_2589790 baseEnd_2589790 := by
    simpa [prefixWord, tailWord_2589790, baseEnd_2589790] using wordTrace_append hprefix tailTrace_2589790
  have hstable : (prefixWord ++ tailWord_2589790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589790).length < 2 ^ (prefixWord ++ tailWord_2589790).sum := by decide
  have hdescent : baseEnd_2589790 < baseStart_2589790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589857 : List Nat := [1, 2, 3, 3, 1, 1, 4, 1, 3, 3]
def baseStart_2589857 : Nat := 118140960795 + 2589857 * 2 ^ 59
def prefixEnd_2589857 : Nat := 4983230072969 + 3 ^ 40 * 2589857 * 2
def baseEnd_2589857 : Nat := 886560978274252604184647

theorem tailTrace_2589857 : CollatzResearch.WordTrace tailWord_2589857 prefixEnd_2589857 886560978274252604184647 := by
  unfold tailWord_2589857
  simp only [CollatzResearch.WordTrace]
  refine ⟨94459844978397876206423825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62973229985598584137615883 94459844978397876206423825)
  ·
    refine ⟨70844883733798407154817869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94459844978397876206423825 70844883733798407154817869)
    ·
      refine ⟨26566831400174402683056701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70844883733798407154817869 26566831400174402683056701)
      ·
        refine ⟨9962561775065401006146263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26566831400174402683056701 9962561775065401006146263)
        ·
          refine ⟨14943842662598101509219395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9962561775065401006146263 14943842662598101509219395)
          ·
            refine ⟨22415763993897152263829093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14943842662598101509219395 22415763993897152263829093)
            ·
              refine ⟨4202955748855716049467955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22415763993897152263829093 4202955748855716049467955)
              ·
                refine ⟨6304433623283574074201933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4202955748855716049467955 6304433623283574074201933)
                ·
                  refine ⟨2364162608731340277825725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6304433623283574074201933 2364162608731340277825725)
                  ·
                    refine ⟨886560978274252604184647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2364162608731340277825725 886560978274252604184647)
                    ·
                      rfl

theorem cell22_2589857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 3, 3].length) (baseStart_2589857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2589857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2589857 prefixEnd_2589857 := by exact prefixLift 2589857
  have htrace : WordTrace (prefixWord ++ tailWord_2589857) baseStart_2589857 baseEnd_2589857 := by
    simpa [prefixWord, tailWord_2589857, baseEnd_2589857] using wordTrace_append hprefix tailTrace_2589857
  have hstable : (prefixWord ++ tailWord_2589857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589857).length < 2 ^ (prefixWord ++ tailWord_2589857).sum := by decide
  have hdescent : baseEnd_2589857 < baseStart_2589857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589868 : List Nat := [2, 2, 1, 1, 1, 1, 1, 5, 1, 7]
def baseStart_2589868 : Nat := 118140960795 + 2589868 * 2 ^ 59
def prefixEnd_2589868 : Nat := 4983230072969 + 3 ^ 40 * 2589868 * 2
def baseEnd_2589868 : Nat := 886564743799052242159613

theorem tailTrace_2589868 : CollatzResearch.WordTrace tailWord_2589868 prefixEnd_2589868 886564743799052242159613 := by
  unfold tailWord_2589868
  simp only [CollatzResearch.WordTrace]
  refine ⟨47230123090679012542537129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62973497454238683390049505 47230123090679012542537129)
  ·
    refine ⟨35422592318009259406902847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47230123090679012542537129 35422592318009259406902847)
    ·
      refine ⟨53133888477013889110354271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35422592318009259406902847 53133888477013889110354271)
      ·
        refine ⟨79700832715520833665531407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53133888477013889110354271 79700832715520833665531407)
        ·
          refine ⟨119551249073281250498297111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79700832715520833665531407 119551249073281250498297111)
          ·
            refine ⟨179326873609921875747445667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119551249073281250498297111 179326873609921875747445667)
            ·
              refine ⟨268990310414882813621168501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179326873609921875747445667 268990310414882813621168501)
              ·
                refine ⟨25217841601395263776984547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 268990310414882813621168501 25217841601395263776984547)
                ·
                  refine ⟨37826762402092895665476821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25217841601395263776984547 37826762402092895665476821)
                  ·
                    refine ⟨886564743799052242159613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37826762402092895665476821 886564743799052242159613)
                    ·
                      rfl

theorem cell22_2589868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_2589868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2589868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2589868 prefixEnd_2589868 := by exact prefixLift 2589868
  have htrace : WordTrace (prefixWord ++ tailWord_2589868) baseStart_2589868 baseEnd_2589868 := by
    simpa [prefixWord, tailWord_2589868, baseEnd_2589868] using wordTrace_append hprefix tailTrace_2589868
  have hstable : (prefixWord ++ tailWord_2589868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589868).length < 2 ^ (prefixWord ++ tailWord_2589868).sum := by decide
  have hdescent : baseEnd_2589868 < baseStart_2589868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589908 : List Nat := [2, 4, 1, 4, 2, 1, 1, 1, 3, 3]
def baseStart_2589908 : Nat := 118140960795 + 2589908 * 2 ^ 59
def prefixEnd_2589908 : Nat := 4983230072969 + 3 ^ 40 * 2589908 * 2
def baseEnd_2589908 : Nat := 886578436616505471159491

theorem tailTrace_2589908 : CollatzResearch.WordTrace tailWord_2589908 prefixEnd_2589908 886578436616505471159491 := by
  unfold tailWord_2589908
  simp only [CollatzResearch.WordTrace]
  refine ⟨47230852550606555958265189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62974470067475407944353585 47230852550606555958265189)
  ·
    refine ⟨8855784853238729242174723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47230852550606555958265189 8855784853238729242174723)
    ·
      refine ⟨13283677279858093863262085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8855784853238729242174723 13283677279858093863262085)
      ·
        refine ⟨2490689489973392599361641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13283677279858093863262085 2490689489973392599361641)
        ·
          refine ⟨1868017117480044449521231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2490689489973392599361641 1868017117480044449521231)
          ·
            refine ⟨2802025676220066674281847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1868017117480044449521231 2802025676220066674281847)
            ·
              refine ⟨4203038514330100011422771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2802025676220066674281847 4203038514330100011422771)
              ·
                refine ⟨6304557771495150017134157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4203038514330100011422771 6304557771495150017134157)
                ·
                  refine ⟨2364209164310681256425309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6304557771495150017134157 2364209164310681256425309)
                  ·
                    refine ⟨886578436616505471159491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2364209164310681256425309 886578436616505471159491)
                    ·
                      rfl

theorem cell22_2589908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_2589908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2589908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2589908 prefixEnd_2589908 := by exact prefixLift 2589908
  have htrace : WordTrace (prefixWord ++ tailWord_2589908) baseStart_2589908 baseEnd_2589908 := by
    simpa [prefixWord, tailWord_2589908, baseEnd_2589908] using wordTrace_append hprefix tailTrace_2589908
  have hstable : (prefixWord ++ tailWord_2589908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589908).length < 2 ^ (prefixWord ++ tailWord_2589908).sum := by decide
  have hdescent : baseEnd_2589908 < baseStart_2589908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589960 : List Nat := [2, 1, 3, 2, 4, 10]
def baseStart_2589960 : Nat := 118140960795 + 2589960 * 2 ^ 59
def prefixEnd_2589960 : Nat := 4983230072969 + 3 ^ 40 * 2589960 * 2
def baseEnd_2589960 : Nat := 10945632559002403319251

theorem tailTrace_2589960 : CollatzResearch.WordTrace tailWord_2589960 prefixEnd_2589960 10945632559002403319251 := by
  unfold tailWord_2589960
  simp only [CollatzResearch.WordTrace]
  refine ⟨47231800848512362398711667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62975734464683149864948889 47231800848512362398711667)
  ·
    refine ⟨70847701272768543598067501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47231800848512362398711667 70847701272768543598067501)
    ·
      refine ⟨26567887977288203849275313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70847701272768543598067501 26567887977288203849275313)
      ·
        refine ⟨19925915982966152886956485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26567887977288203849275313 19925915982966152886956485)
        ·
          refine ⟨3736109246806153666304341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19925915982966152886956485 3736109246806153666304341)
          ·
            refine ⟨10945632559002403319251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3736109246806153666304341 10945632559002403319251)
            ·
              rfl

theorem cell22_2589960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 10].length) (baseStart_2589960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2589960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2589960 prefixEnd_2589960 := by exact prefixLift 2589960
  have htrace : WordTrace (prefixWord ++ tailWord_2589960) baseStart_2589960 baseEnd_2589960 := by
    simpa [prefixWord, tailWord_2589960, baseEnd_2589960] using wordTrace_append hprefix tailTrace_2589960
  have hstable : (prefixWord ++ tailWord_2589960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589960).length < 2 ^ (prefixWord ++ tailWord_2589960).sum := by decide
  have hdescent : baseEnd_2589960 < baseStart_2589960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589964 : List Nat := [2, 2, 1, 2, 2, 4, 2, 2, 2, 3]
def baseStart_2589964 : Nat := 118140960795 + 2589964 * 2 ^ 59
def prefixEnd_2589964 : Nat := 4983230072969 + 3 ^ 40 * 2589964 * 2
def baseEnd_2589964 : Nat := 886597606560939991759319

theorem tailTrace_2589964 : CollatzResearch.WordTrace tailWord_2589964 prefixEnd_2589964 886597606560939991759319 := by
  unfold tailWord_2589964
  simp only [CollatzResearch.WordTrace]
  refine ⟨47231873794505116740284473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62975831726006822320379297 47231873794505116740284473)
  ·
    refine ⟨35423905345878837555213355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47231873794505116740284473 35423905345878837555213355)
    ·
      refine ⟨53135858018818256332820033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35423905345878837555213355 53135858018818256332820033)
      ·
        refine ⟨39851893514113692249615025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53135858018818256332820033 39851893514113692249615025)
        ·
          refine ⟨29888920135585269187211269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39851893514113692249615025 29888920135585269187211269)
          ·
            refine ⟨5604172525422237972602113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29888920135585269187211269 5604172525422237972602113)
            ·
              refine ⟨4203129394066678479451585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5604172525422237972602113 4203129394066678479451585)
              ·
                refine ⟨3152347045550008859588689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4203129394066678479451585 3152347045550008859588689)
                ·
                  refine ⟨2364260284162506644691517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3152347045550008859588689 2364260284162506644691517)
                  ·
                    refine ⟨886597606560939991759319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2364260284162506644691517 886597606560939991759319)
                    ·
                      rfl

theorem cell22_2589964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 2, 2, 3].length) (baseStart_2589964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2589964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2589964 prefixEnd_2589964 := by exact prefixLift 2589964
  have htrace : WordTrace (prefixWord ++ tailWord_2589964) baseStart_2589964 baseEnd_2589964 := by
    simpa [prefixWord, tailWord_2589964, baseEnd_2589964] using wordTrace_append hprefix tailTrace_2589964
  have hstable : (prefixWord ++ tailWord_2589964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589964).length < 2 ^ (prefixWord ++ tailWord_2589964).sum := by decide
  have hdescent : baseEnd_2589964 < baseStart_2589964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589966 : List Nat := [4, 1, 1, 2, 1, 5, 2, 2, 4]
def baseStart_2589966 : Nat := 118140960795 + 2589966 * 2 ^ 59
def prefixEnd_2589966 : Nat := 4983230072969 + 3 ^ 40 * 2589966 * 2
def baseEnd_2589966 : Nat := 295532763733937551069771

theorem tailTrace_2589966 : CollatzResearch.WordTrace tailWord_2589966 prefixEnd_2589966 295532763733937551069771 := by
  unfold tailWord_2589966
  simp only [CollatzResearch.WordTrace]
  refine ⟨11807977566875373477767719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62975880356668658548094501 11807977566875373477767719)
  ·
    refine ⟨17711966350313060216651579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11807977566875373477767719 17711966350313060216651579)
    ·
      refine ⟨26567949525469590324977369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17711966350313060216651579 26567949525469590324977369)
      ·
        refine ⟨19925962144102192743733027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26567949525469590324977369 19925962144102192743733027)
        ·
          refine ⟨29888943216153289115599541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19925962144102192743733027 29888943216153289115599541)
          ·
            refine ⟨2802088426514370854587457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29888943216153289115599541 2802088426514370854587457)
            ·
              refine ⟨2101566319885778140940593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2802088426514370854587457 2101566319885778140940593)
              ·
                refine ⟨1576174739914333605705445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2101566319885778140940593 1576174739914333605705445)
                ·
                  refine ⟨295532763733937551069771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1576174739914333605705445 295532763733937551069771)
                  ·
                    rfl

theorem cell22_2589966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 2, 4].length) (baseStart_2589966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2589966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2589966 prefixEnd_2589966 := by exact prefixLift 2589966
  have htrace : WordTrace (prefixWord ++ tailWord_2589966) baseStart_2589966 baseEnd_2589966 := by
    simpa [prefixWord, tailWord_2589966, baseEnd_2589966] using wordTrace_append hprefix tailTrace_2589966
  have hstable : (prefixWord ++ tailWord_2589966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589966).length < 2 ^ (prefixWord ++ tailWord_2589966).sum := by decide
  have hdescent : baseEnd_2589966 < baseStart_2589966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589994 : List Nat := [3, 1, 4, 2, 1, 2, 3, 6]
def baseStart_2589994 : Nat := 118140960795 + 2589994 * 2 ^ 59
def prefixEnd_2589994 : Nat := 4983230072969 + 3 ^ 40 * 2589994 * 2
def baseEnd_2589994 : Nat := 98511986241558879278803

theorem tailTrace_2589994 : CollatzResearch.WordTrace tailWord_2589994 prefixEnd_2589994 98511986241558879278803 := by
  unfold tailWord_2589994
  simp only [CollatzResearch.WordTrace]
  refine ⟨23616210444725387151040259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62976561185934365736107357 23616210444725387151040259)
  ·
    refine ⟨35424315667088080726560389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23616210444725387151040259 35424315667088080726560389)
    ·
      refine ⟨6642059187579015136230073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35424315667088080726560389 6642059187579015136230073)
      ·
        refine ⟨4981544390684261352172555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6642059187579015136230073 4981544390684261352172555)
        ·
          refine ⟨7472316586026392028258833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4981544390684261352172555 7472316586026392028258833)
          ·
            refine ⟨5604237439519794021194125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7472316586026392028258833 5604237439519794021194125)
            ·
              refine ⟨2101589039819922757947797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5604237439519794021194125 2101589039819922757947797)
              ·
                refine ⟨98511986241558879278803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2101589039819922757947797 98511986241558879278803)
                ·
                  rfl

theorem cell22_2589994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 6].length) (baseStart_2589994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2589994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2589994 prefixEnd_2589994 := by exact prefixLift 2589994
  have htrace : WordTrace (prefixWord ++ tailWord_2589994) baseStart_2589994 baseEnd_2589994 := by
    simpa [prefixWord, tailWord_2589994, baseEnd_2589994] using wordTrace_append hprefix tailTrace_2589994
  have hstable : (prefixWord ++ tailWord_2589994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589994).length < 2 ^ (prefixWord ++ tailWord_2589994).sum := by decide
  have hdescent : baseEnd_2589994 < baseStart_2589994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590037 : List Nat := [1, 3, 2, 2, 3, 1, 2, 1, 2, 5]
def baseStart_2590037 : Nat := 118140960795 + 2590037 * 2 ^ 59
def prefixEnd_2590037 : Nat := 4983230072969 + 3 ^ 40 * 2590037 * 2
def baseEnd_2590037 : Nat := 886622595952792134684095

theorem tailTrace_2590037 : CollatzResearch.WordTrace tailWord_2590037 prefixEnd_2590037 886622595952792134684095 := by
  unfold tailWord_2590037
  simp only [CollatzResearch.WordTrace]
  refine ⟨94466410117745766947976365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62977606745163844631984243 94466410117745766947976365)
  ·
    refine ⟨35424903794154662605491137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94466410117745766947976365 35424903794154662605491137)
    ·
      refine ⟨26568677845615996954118353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35424903794154662605491137 26568677845615996954118353)
      ·
        refine ⟨19926508384211997715588765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26568677845615996954118353 19926508384211997715588765)
        ·
          refine ⟨7472440644079499143345787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19926508384211997715588765 7472440644079499143345787)
          ·
            refine ⟨11208660966119248715018681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7472440644079499143345787 11208660966119248715018681)
            ·
              refine ⟨8406495724589436536264011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11208660966119248715018681 8406495724589436536264011)
              ·
                refine ⟨12609743586884154804396017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8406495724589436536264011 12609743586884154804396017)
                ·
                  refine ⟨9457307690163116103297013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12609743586884154804396017 9457307690163116103297013)
                  ·
                    refine ⟨886622595952792134684095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9457307690163116103297013 886622595952792134684095)
                    ·
                      rfl

theorem cell22_2590037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_2590037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2590037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2590037 prefixEnd_2590037 := by exact prefixLift 2590037
  have htrace : WordTrace (prefixWord ++ tailWord_2590037) baseStart_2590037 baseEnd_2590037 := by
    simpa [prefixWord, tailWord_2590037, baseEnd_2590037] using wordTrace_append hprefix tailTrace_2590037
  have hstable : (prefixWord ++ tailWord_2590037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590037).length < 2 ^ (prefixWord ++ tailWord_2590037).sum := by decide
  have hdescent : baseEnd_2590037 < baseStart_2590037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590039 : List Nat := [1, 1, 3, 2, 3, 3, 3, 1, 5]
def baseStart_2590039 : Nat := 118140960795 + 2590039 * 2 ^ 59
def prefixEnd_2590039 : Nat := 4983230072969 + 3 ^ 40 * 2590039 * 2
def baseEnd_2590039 : Nat := 295541093531221598711363

theorem tailTrace_2590039 : CollatzResearch.WordTrace tailWord_2590039 prefixEnd_2590039 295541093531221598711363 := by
  unfold tailWord_2590039
  simp only [CollatzResearch.WordTrace]
  refine ⟨94466483063738521289549171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62977655375825680859699447 94466483063738521289549171)
  ·
    refine ⟨141699724595607781934323757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94466483063738521289549171 141699724595607781934323757)
    ·
      refine ⟨53137396723352918225371409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141699724595607781934323757 53137396723352918225371409)
      ·
        refine ⟨39853047542514688669028557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53137396723352918225371409 39853047542514688669028557)
        ·
          refine ⟨14944892828443008250885709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39853047542514688669028557 14944892828443008250885709)
          ·
            refine ⟨5604334810666128094082141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14944892828443008250885709 5604334810666128094082141)
            ·
              refine ⟨2101625553999798035280803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5604334810666128094082141 2101625553999798035280803)
              ·
                refine ⟨3152438330999697052921205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2101625553999798035280803 3152438330999697052921205)
                ·
                  refine ⟨295541093531221598711363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3152438330999697052921205 295541093531221598711363)
                  ·
                    rfl

theorem cell22_2590039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 1, 5].length) (baseStart_2590039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2590039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2590039 prefixEnd_2590039 := by exact prefixLift 2590039
  have htrace : WordTrace (prefixWord ++ tailWord_2590039) baseStart_2590039 baseEnd_2590039 := by
    simpa [prefixWord, tailWord_2590039, baseEnd_2590039] using wordTrace_append hprefix tailTrace_2590039
  have hstable : (prefixWord ++ tailWord_2590039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590039).length < 2 ^ (prefixWord ++ tailWord_2590039).sum := by decide
  have hdescent : baseEnd_2590039 < baseStart_2590039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590045 : List Nat := [1, 4, 5, 1, 2, 1, 2, 6]
def baseStart_2590045 : Nat := 118140960795 + 2590045 * 2 ^ 59
def prefixEnd_2590045 : Nat := 4983230072969 + 3 ^ 40 * 2590045 * 2
def baseEnd_2590045 : Nat := 98513926057364753387119

theorem tailTrace_2590045 : CollatzResearch.WordTrace tailWord_2590045 prefixEnd_2590045 98513926057364753387119 := by
  unfold tailWord_2590045
  simp only [CollatzResearch.WordTrace]
  refine ⟨94466701901716784314267589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62977801267811189542845059 94466701901716784314267589)
  ·
    refine ⟨17712506606571897058925173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94466701901716784314267589 17712506606571897058925173)
    ·
      refine ⟨1660547494366115349274235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17712506606571897058925173 1660547494366115349274235)
      ·
        refine ⟨2490821241549173023911353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1660547494366115349274235 2490821241549173023911353)
        ·
          refine ⟨1868115931161879767933515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2490821241549173023911353 1868115931161879767933515)
          ·
            refine ⟨2802173896742819651900273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1868115931161879767933515 2802173896742819651900273)
            ·
              refine ⟨2101630422557114738925205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2802173896742819651900273 2101630422557114738925205)
              ·
                refine ⟨98513926057364753387119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2101630422557114738925205 98513926057364753387119)
                ·
                  rfl

theorem cell22_2590045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 6].length) (baseStart_2590045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2590045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2590045 prefixEnd_2590045 := by exact prefixLift 2590045
  have htrace : WordTrace (prefixWord ++ tailWord_2590045) baseStart_2590045 baseEnd_2590045 := by
    simpa [prefixWord, tailWord_2590045, baseEnd_2590045] using wordTrace_append hprefix tailTrace_2590045
  have hstable : (prefixWord ++ tailWord_2590045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590045).length < 2 ^ (prefixWord ++ tailWord_2590045).sum := by decide
  have hdescent : baseEnd_2590045 < baseStart_2590045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590084 : List Nat := [2, 3, 2, 1, 1, 5, 1, 1, 6]
def baseStart_2590084 : Nat := 118140960795 + 2590084 * 2 ^ 59
def prefixEnd_2590084 : Nat := 4983230072969 + 3 ^ 40 * 2590084 * 2
def baseEnd_2590084 : Nat := 295546228337766559586317

theorem tailTrace_2590084 : CollatzResearch.WordTrace tailWord_2590084 prefixEnd_2590084 295546228337766559586317 := by
  unfold tailWord_2590084
  simp only [CollatzResearch.WordTrace]
  refine ⟨47234062174287746987468653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62978749565716995983291537 47234062174287746987468653)
  ·
    refine ⟨17712773315357905120300745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47234062174287746987468653 17712773315357905120300745)
    ·
      refine ⟨13284579986518428840225559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17712773315357905120300745 13284579986518428840225559)
      ·
        refine ⟨19926869979777643260338339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13284579986518428840225559 19926869979777643260338339)
        ·
          refine ⟨29890304969666464890507509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19926869979777643260338339 29890304969666464890507509)
          ·
            refine ⟨2802216090906231083485079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29890304969666464890507509 2802216090906231083485079)
            ·
              refine ⟨4203324136359346625227619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2802216090906231083485079 4203324136359346625227619)
              ·
                refine ⟨6304986204539019937841429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4203324136359346625227619 6304986204539019937841429)
                ·
                  refine ⟨295546228337766559586317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6304986204539019937841429 295546228337766559586317)
                  ·
                    rfl

theorem cell22_2590084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 6].length) (baseStart_2590084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2590084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2590084 prefixEnd_2590084 := by exact prefixLift 2590084
  have htrace : WordTrace (prefixWord ++ tailWord_2590084) baseStart_2590084 baseEnd_2590084 := by
    simpa [prefixWord, tailWord_2590084, baseEnd_2590084] using wordTrace_append hprefix tailTrace_2590084
  have hstable : (prefixWord ++ tailWord_2590084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590084).length < 2 ^ (prefixWord ++ tailWord_2590084).sum := by decide
  have hdescent : baseEnd_2590084 < baseStart_2590084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590114 : List Nat := [3, 3, 1, 2, 1, 2, 1, 3, 2, 4]
def baseStart_2590114 : Nat := 118140960795 + 2590114 * 2 ^ 59
def prefixEnd_2590114 : Nat := 4983230072969 + 3 ^ 40 * 2590114 * 2
def baseEnd_2590114 : Nat := 886648954626389600508859

theorem tailTrace_2590114 : CollatzResearch.WordTrace tailWord_2590114 prefixEnd_2590114 886648954626389600508859 := by
  unfold tailWord_2590114
  simp only [CollatzResearch.WordTrace]
  refine ⟨23617304634616702274632349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62979479025644539399019597 23617304634616702274632349)
  ·
    refine ⟨8856489237981263352987131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23617304634616702274632349 8856489237981263352987131)
    ·
      refine ⟨13284733856971895029480697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8856489237981263352987131 13284733856971895029480697)
      ·
        refine ⟨9963550392728921272110523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13284733856971895029480697 9963550392728921272110523)
        ·
          refine ⟨14945325589093381908165785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9963550392728921272110523 14945325589093381908165785)
          ·
            refine ⟨11208994191820036431124339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14945325589093381908165785 11208994191820036431124339)
            ·
              refine ⟨16813491287730054646686509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11208994191820036431124339 16813491287730054646686509)
              ·
                refine ⟨6305059232898770492507441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16813491287730054646686509 6305059232898770492507441)
                ·
                  refine ⟨4728794424674077869380581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6305059232898770492507441 4728794424674077869380581)
                  ·
                    refine ⟨886648954626389600508859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4728794424674077869380581 886648954626389600508859)
                    ·
                      rfl

theorem cell22_2590114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_2590114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2590114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2590114 prefixEnd_2590114 := by exact prefixLift 2590114
  have htrace : WordTrace (prefixWord ++ tailWord_2590114) baseStart_2590114 baseEnd_2590114 := by
    simpa [prefixWord, tailWord_2590114, baseEnd_2590114] using wordTrace_append hprefix tailTrace_2590114
  have hstable : (prefixWord ++ tailWord_2590114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590114).length < 2 ^ (prefixWord ++ tailWord_2590114).sum := by decide
  have hdescent : baseEnd_2590114 < baseStart_2590114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590187 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 5, 4]
def baseStart_2590187 : Nat := 118140960795 + 2590187 * 2 ^ 59
def prefixEnd_2590187 : Nat := 4983230072969 + 3 ^ 40 * 2590187 * 2
def baseEnd_2590187 : Nat := 886673944018241743433635

theorem tailTrace_2590187 : CollatzResearch.WordTrace tailWord_2590187 prefixEnd_2590187 886673944018241743433635 := by
  unfold tailWord_2590187
  simp only [CollatzResearch.WordTrace]
  refine ⟨94471881067202342565936815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62981254044801561710624543 94471881067202342565936815)
  ·
    refine ⟨141707821600803513848905223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94471881067202342565936815 141707821600803513848905223)
    ·
      refine ⟨212561732401205270773357835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141707821600803513848905223 212561732401205270773357835)
      ·
        refine ⟨318842598601807906160036753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212561732401205270773357835 318842598601807906160036753)
        ·
          refine ⟨239131948951355929620027565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 318842598601807906160036753 239131948951355929620027565)
          ·
            refine ⟨89674480856758473607510337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 239131948951355929620027565 89674480856758473607510337)
            ·
              refine ⟨67255860642568855205632753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89674480856758473607510337 67255860642568855205632753)
              ·
                refine ⟨50441895481926641404224565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67255860642568855205632753 50441895481926641404224565)
                ·
                  refine ⟨4728927701430622631646053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50441895481926641404224565 4728927701430622631646053)
                  ·
                    refine ⟨886673944018241743433635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4728927701430622631646053 886673944018241743433635)
                    ·
                      rfl

theorem cell22_2590187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 5, 4].length) (baseStart_2590187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2590187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2590187 prefixEnd_2590187 := by exact prefixLift 2590187
  have htrace : WordTrace (prefixWord ++ tailWord_2590187) baseStart_2590187 baseEnd_2590187 := by
    simpa [prefixWord, tailWord_2590187, baseEnd_2590187] using wordTrace_append hprefix tailTrace_2590187
  have hstable : (prefixWord ++ tailWord_2590187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590187).length < 2 ^ (prefixWord ++ tailWord_2590187).sum := by decide
  have hdescent : baseEnd_2590187 < baseStart_2590187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590264 : List Nat := [2, 1, 2, 1, 4, 3, 2, 7]
def baseStart_2590264 : Nat := 118140960795 + 2590264 * 2 ^ 59
def prefixEnd_2590264 : Nat := 4983230072969 + 3 ^ 40 * 2590264 * 2
def baseEnd_2590264 : Nat := 98522255854648801028711

theorem tailTrace_2590264 : CollatzResearch.WordTrace tailWord_2590264 prefixEnd_2590264 98522255854648801028711 := by
  unfold tailWord_2590264
  simp only [CollatzResearch.WordTrace]
  refine ⟨47237344743961692358244923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62983126325282256477659897 47237344743961692358244923)
  ·
    refine ⟨70856017115942538537367385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47237344743961692358244923 70856017115942538537367385)
    ·
      refine ⟨53142012836956903903025539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70856017115942538537367385 53142012836956903903025539)
      ·
        refine ⟨79713019255435355854538309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53142012836956903903025539 79713019255435355854538309)
        ·
          refine ⟨14946191110394129222725933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79713019255435355854538309 14946191110394129222725933)
          ·
            refine ⟨5604821666397798458522225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14946191110394129222725933 5604821666397798458522225)
            ·
              refine ⟨4203616249798348843891669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5604821666397798458522225 4203616249798348843891669)
              ·
                refine ⟨98522255854648801028711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4203616249798348843891669 98522255854648801028711)
                ·
                  rfl

theorem cell22_2590264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 7].length) (baseStart_2590264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2590264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2590264 prefixEnd_2590264 := by exact prefixLift 2590264
  have htrace : WordTrace (prefixWord ++ tailWord_2590264) baseStart_2590264 baseEnd_2590264 := by
    simpa [prefixWord, tailWord_2590264, baseEnd_2590264] using wordTrace_append hprefix tailTrace_2590264
  have hstable : (prefixWord ++ tailWord_2590264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590264).length < 2 ^ (prefixWord ++ tailWord_2590264).sum := by decide
  have hdescent : baseEnd_2590264 < baseStart_2590264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590268 : List Nat := [2, 2, 2, 2, 4, 1, 1, 3, 2, 3]
def baseStart_2590268 : Nat := 118140960795 + 2590268 * 2 ^ 59
def prefixEnd_2590268 : Nat := 4983230072969 + 3 ^ 40 * 2590268 * 2
def baseEnd_2590268 : Nat := 886701671973584532158387

theorem tailTrace_2590268 : CollatzResearch.WordTrace tailWord_2590268 prefixEnd_2590268 886701671973584532158387 := by
  unfold tailWord_2590268
  simp only [CollatzResearch.WordTrace]
  refine ⟨47237417689954446699817729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62983223586605928933090305 47237417689954446699817729)
  ·
    refine ⟨35428063267465835024863297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47237417689954446699817729 35428063267465835024863297)
    ·
      refine ⟨26571047450599376268647473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35428063267465835024863297 26571047450599376268647473)
      ·
        refine ⟨19928285587949532201485605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26571047450599376268647473 19928285587949532201485605)
        ·
          refine ⟨3736553547740537287778551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19928285587949532201485605 3736553547740537287778551)
          ·
            refine ⟨5604830321610805931667827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3736553547740537287778551 5604830321610805931667827)
            ·
              refine ⟨8407245482416208897501741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5604830321610805931667827 8407245482416208897501741)
              ·
                refine ⟨3152717055906078336563153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8407245482416208897501741 3152717055906078336563153)
                ·
                  refine ⟨2364537791929558752422365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3152717055906078336563153 2364537791929558752422365)
                  ·
                    refine ⟨886701671973584532158387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2364537791929558752422365 886701671973584532158387)
                    ·
                      rfl

theorem cell22_2590268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 3, 2, 3].length) (baseStart_2590268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2590268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2590268 prefixEnd_2590268 := by exact prefixLift 2590268
  have htrace : WordTrace (prefixWord ++ tailWord_2590268) baseStart_2590268 baseEnd_2590268 := by
    simpa [prefixWord, tailWord_2590268, baseEnd_2590268] using wordTrace_append hprefix tailTrace_2590268
  have hstable : (prefixWord ++ tailWord_2590268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590268).length < 2 ^ (prefixWord ++ tailWord_2590268).sum := by decide
  have hdescent : baseEnd_2590268 < baseStart_2590268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590371 : List Nat := [1, 1, 1, 4, 1, 1, 3, 6, 4]
def baseStart_2590371 : Nat := 118140960795 + 2590371 * 2 ^ 59
def prefixEnd_2590371 : Nat := 4983230072969 + 3 ^ 40 * 2590371 * 2
def baseEnd_2590371 : Nat := 295578976992842198944357

theorem tailTrace_2590371 : CollatzResearch.WordTrace tailWord_2590371 prefixEnd_2590371 295578976992842198944357 := by
  unfold tailWord_2590371
  simp only [CollatzResearch.WordTrace]
  refine ⟨94478592098535741990634967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62985728065690494660423311 94478592098535741990634967)
  ·
    refine ⟨141717888147803612985952451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94478592098535741990634967 141717888147803612985952451)
    ·
      refine ⟨212576832221705419478928677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141717888147803612985952451 212576832221705419478928677)
      ·
        refine ⟨39858156041569766152299127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 212576832221705419478928677 39858156041569766152299127)
        ·
          refine ⟨59787234062354649228448691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39858156041569766152299127 59787234062354649228448691)
          ·
            refine ⟨89680851093531973842673037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59787234062354649228448691 89680851093531973842673037)
            ·
              refine ⟨33630319160074490191002389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89680851093531973842673037 33630319160074490191002389)
              ·
                refine ⟨1576421210628491727703237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33630319160074490191002389 1576421210628491727703237)
                ·
                  refine ⟨295578976992842198944357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1576421210628491727703237 295578976992842198944357)
                  ·
                    rfl

theorem cell22_2590371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 6, 4].length) (baseStart_2590371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2590371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2590371 prefixEnd_2590371 := by exact prefixLift 2590371
  have htrace : WordTrace (prefixWord ++ tailWord_2590371) baseStart_2590371 baseEnd_2590371 := by
    simpa [prefixWord, tailWord_2590371, baseEnd_2590371] using wordTrace_append hprefix tailTrace_2590371
  have hstable : (prefixWord ++ tailWord_2590371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590371).length < 2 ^ (prefixWord ++ tailWord_2590371).sum := by decide
  have hdescent : baseEnd_2590371 < baseStart_2590371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590384 : List Nat := [2, 1, 1, 1, 2, 1, 5, 2, 1, 6]
def baseStart_2590384 : Nat := 118140960795 + 2590384 * 2 ^ 59
def prefixEnd_2590384 : Nat := 4983230072969 + 3 ^ 40 * 2590384 * 2
def baseEnd_2590384 : Nat := 886741381144198896258031

theorem tailTrace_2590384 : CollatzResearch.WordTrace tailWord_2590384 prefixEnd_2590384 886741381144198896258031 := by
  unfold tailWord_2590384
  simp only [CollatzResearch.WordTrace]
  refine ⟨47239533123744322605429103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62986044164992430140572137 47239533123744322605429103)
  ·
    refine ⟨70859299685616483908143655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47239533123744322605429103 70859299685616483908143655)
    ·
      refine ⟨106288949528424725862215483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70859299685616483908143655 106288949528424725862215483)
      ·
        refine ⟨159433424292637088793323225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106288949528424725862215483 159433424292637088793323225)
        ·
          refine ⟨119575068219477816594992419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159433424292637088793323225 119575068219477816594992419)
          ·
            refine ⟨179362602329216724892488629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119575068219477816594992419 179362602329216724892488629)
            ·
              refine ⟨16815243968364067958670809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 179362602329216724892488629 16815243968364067958670809)
              ·
                refine ⟨12611432976273050969003107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16815243968364067958670809 12611432976273050969003107)
                ·
                  refine ⟨18917149464409576453504661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12611432976273050969003107 18917149464409576453504661)
                  ·
                    refine ⟨886741381144198896258031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18917149464409576453504661 886741381144198896258031)
                    ·
                      rfl

theorem cell22_2590384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 1, 6].length) (baseStart_2590384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2590384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2590384 prefixEnd_2590384 := by exact prefixLift 2590384
  have htrace : WordTrace (prefixWord ++ tailWord_2590384) baseStart_2590384 baseEnd_2590384 := by
    simpa [prefixWord, tailWord_2590384, baseEnd_2590384] using wordTrace_append hprefix tailTrace_2590384
  have hstable : (prefixWord ++ tailWord_2590384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590384).length < 2 ^ (prefixWord ++ tailWord_2590384).sum := by decide
  have hdescent : baseEnd_2590384 < baseStart_2590384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590386 : List Nat := [3, 2, 1, 1, 1, 2, 5, 1, 1, 5]
def baseStart_2590386 : Nat := 118140960795 + 2590386 * 2 ^ 59
def prefixEnd_2590386 : Nat := 4983230072969 + 3 ^ 40 * 2590386 * 2
def baseEnd_2590386 : Nat := 886742065785071557708025

theorem tailTrace_2590386 : CollatzResearch.WordTrace tailWord_2590386 prefixEnd_2590386 886742065785071557708025 := by
  unfold tailWord_2590386
  simp only [CollatzResearch.WordTrace]
  refine ⟨23619784798370349888107753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62986092795654266368287341 23619784798370349888107753)
  ·
    refine ⟨17714838598777762416080815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23619784798370349888107753 17714838598777762416080815)
    ·
      refine ⟨26572257898166643624121223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17714838598777762416080815 26572257898166643624121223)
      ·
        refine ⟨39858386847249965436181835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26572257898166643624121223 39858386847249965436181835)
        ·
          refine ⟨59787580270874948154272753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39858386847249965436181835 59787580270874948154272753)
          ·
            refine ⟨44840685203156211115704565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59787580270874948154272753 44840685203156211115704565)
            ·
              refine ⟨4203814237795894792097303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44840685203156211115704565 4203814237795894792097303)
              ·
                refine ⟨6305721356693842188145955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4203814237795894792097303 6305721356693842188145955)
                ·
                  refine ⟨9458582035040763282218933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6305721356693842188145955 9458582035040763282218933)
                  ·
                    refine ⟨886742065785071557708025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9458582035040763282218933 886742065785071557708025)
                    ·
                      rfl

theorem cell22_2590386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_2590386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2590386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2590386 prefixEnd_2590386 := by exact prefixLift 2590386
  have htrace : WordTrace (prefixWord ++ tailWord_2590386) baseStart_2590386 baseEnd_2590386 := by
    simpa [prefixWord, tailWord_2590386, baseEnd_2590386] using wordTrace_append hprefix tailTrace_2590386
  have hstable : (prefixWord ++ tailWord_2590386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590386).length < 2 ^ (prefixWord ++ tailWord_2590386).sum := by decide
  have hdescent : baseEnd_2590386 < baseStart_2590386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590390 : List Nat := [5, 1, 3, 1, 1, 1, 1, 4, 1, 4]
def baseStart_2590390 : Nat := 118140960795 + 2590390 * 2 ^ 59
def prefixEnd_2590390 : Nat := 4983230072969 + 3 ^ 40 * 2590390 * 2
def baseEnd_2590390 : Nat := 886743435066816880608013

theorem tailTrace_2590390 : CollatzResearch.WordTrace tailWord_2590390 prefixEnd_2590390 886743435066816880608013 := by
  unfold tailWord_2590390
  simp only [CollatzResearch.WordTrace]
  refine ⟨5904955317841681764723539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62986190056977938823717749 5904955317841681764723539)
  ·
    refine ⟨8857432976762522647085309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5904955317841681764723539 8857432976762522647085309)
    ·
      refine ⟨3321537366285945992656991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8857432976762522647085309 3321537366285945992656991)
      ·
        refine ⟨4982306049428918988985487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3321537366285945992656991 4982306049428918988985487)
        ·
          refine ⟨7473459074143378483478231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4982306049428918988985487 7473459074143378483478231)
          ·
            refine ⟨11210188611215067725217347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7473459074143378483478231 11210188611215067725217347)
            ·
              refine ⟨16815282916822601587826021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11210188611215067725217347 16815282916822601587826021)
              ·
                refine ⟨3152865546904237797717379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16815282916822601587826021 3152865546904237797717379)
                ·
                  refine ⟨4729298320356356696576069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3152865546904237797717379 4729298320356356696576069)
                  ·
                    refine ⟨886743435066816880608013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4729298320356356696576069 886743435066816880608013)
                    ·
                      rfl

theorem cell22_2590390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_2590390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2590390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2590390 prefixEnd_2590390 := by exact prefixLift 2590390
  have htrace : WordTrace (prefixWord ++ tailWord_2590390) baseStart_2590390 baseEnd_2590390 := by
    simpa [prefixWord, tailWord_2590390, baseEnd_2590390] using wordTrace_append hprefix tailTrace_2590390
  have hstable : (prefixWord ++ tailWord_2590390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590390).length < 2 ^ (prefixWord ++ tailWord_2590390).sum := by decide
  have hdescent : baseEnd_2590390 < baseStart_2590390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590399 : List Nat := [1, 1, 2, 2, 2, 3, 3, 8]
def baseStart_2590399 : Nat := 118140960795 + 2590399 * 2 ^ 59
def prefixEnd_2590399 : Nat := 4983230072969 + 3 ^ 40 * 2590399 * 2
def baseEnd_2590399 : Nat := 98527390661193761903665

theorem tailTrace_2590399 : CollatzResearch.WordTrace tailWord_2590399 prefixEnd_2590399 98527390661193761903665 := by
  unfold tailWord_2590399
  simp only [CollatzResearch.WordTrace]
  refine ⟨94479613342434302772654251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62986408894956201848436167 94479613342434302772654251)
  ·
    refine ⟨141719420013651454158981377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94479613342434302772654251 141719420013651454158981377)
    ·
      refine ⟨106289565010238590619236033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141719420013651454158981377 106289565010238590619236033)
      ·
        refine ⟨79717173757678942964427025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106289565010238590619236033 79717173757678942964427025)
        ·
          refine ⟨59787880318259207223320269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79717173757678942964427025 59787880318259207223320269)
          ·
            refine ⟨22420455119347202708745101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59787880318259207223320269 22420455119347202708745101)
            ·
              refine ⟨8407670669755201015779413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22420455119347202708745101 8407670669755201015779413)
              ·
                refine ⟨98527390661193761903665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8407670669755201015779413 98527390661193761903665)
                ·
                  rfl

theorem cell22_2590399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 8].length) (baseStart_2590399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2590399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2590399 prefixEnd_2590399 := by exact prefixLift 2590399
  have htrace : WordTrace (prefixWord ++ tailWord_2590399) baseStart_2590399 baseEnd_2590399 := by
    simpa [prefixWord, tailWord_2590399, baseEnd_2590399] using wordTrace_append hprefix tailTrace_2590399
  have hstable : (prefixWord ++ tailWord_2590399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590399).length < 2 ^ (prefixWord ++ tailWord_2590399).sum := by decide
  have hdescent : baseEnd_2590399 < baseStart_2590399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590418 : List Nat := [3, 2, 2, 2, 2, 2, 1, 2, 2, 4]
def baseStart_2590418 : Nat := 118140960795 + 2590418 * 2 ^ 59
def prefixEnd_2590418 : Nat := 4983230072969 + 3 ^ 40 * 2590418 * 2
def baseEnd_2590418 : Nat := 886753020039034140907927

theorem tailTrace_2590418 : CollatzResearch.WordTrace tailWord_2590418 prefixEnd_2590418 886753020039034140907927 := by
  unfold tailWord_2590418
  simp only [CollatzResearch.WordTrace]
  refine ⟨23620076582341367254398977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62986870886243646011730605 23620076582341367254398977)
  ·
    refine ⟨17715057436756025440799233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23620076582341367254398977 17715057436756025440799233)
    ·
      refine ⟨13286293077567019080599425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17715057436756025440799233 13286293077567019080599425)
      ·
        refine ⟨9964719808175264310449569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13286293077567019080599425 9964719808175264310449569)
        ·
          refine ⟨7473539856131448232837177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9964719808175264310449569 7473539856131448232837177)
          ·
            refine ⟨5605154892098586174627883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7473539856131448232837177 5605154892098586174627883)
            ·
              refine ⟨8407732338147879261941825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5605154892098586174627883 8407732338147879261941825)
              ·
                refine ⟨6305799253610909446456369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8407732338147879261941825 6305799253610909446456369)
                ·
                  refine ⟨4729349440208182084842277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6305799253610909446456369 4729349440208182084842277)
                  ·
                    refine ⟨886753020039034140907927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4729349440208182084842277 886753020039034140907927)
                    ·
                      rfl

theorem cell22_2590418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_2590418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2590418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2590418 prefixEnd_2590418 := by exact prefixLift 2590418
  have htrace : WordTrace (prefixWord ++ tailWord_2590418) baseStart_2590418 baseEnd_2590418 := by
    simpa [prefixWord, tailWord_2590418, baseEnd_2590418] using wordTrace_append hprefix tailTrace_2590418
  have hstable : (prefixWord ++ tailWord_2590418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590418).length < 2 ^ (prefixWord ++ tailWord_2590418).sum := by decide
  have hdescent : baseEnd_2590418 < baseStart_2590418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590422 : List Nat := [5, 2, 1, 3, 1, 2, 1, 1, 6]
def baseStart_2590422 : Nat := 118140960795 + 2590422 * 2 ^ 59
def prefixEnd_2590422 : Nat := 4983230072969 + 3 ^ 40 * 2590422 * 2
def baseEnd_2590422 : Nat := 295584796440259821269305

theorem tailTrace_2590422 : CollatzResearch.WordTrace tailWord_2590422 prefixEnd_2590422 295584796440259821269305 := by
  unfold tailWord_2590422
  simp only [CollatzResearch.WordTrace]
  refine ⟨5905028263834436106296345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62986968147567318467161013 5905028263834436106296345)
  ·
    refine ⟨4428771197875827079722259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5905028263834436106296345 4428771197875827079722259)
    ·
      refine ⟨6643156796813740619583389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4428771197875827079722259 6643156796813740619583389)
      ·
        refine ⟨2491183798805152732343771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6643156796813740619583389 2491183798805152732343771)
        ·
          refine ⟨3736775698207729098515657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2491183798805152732343771 3736775698207729098515657)
          ·
            refine ⟨2802581773655796823886743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3736775698207729098515657 2802581773655796823886743)
            ·
              refine ⟨4203872660483695235830115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2802581773655796823886743 4203872660483695235830115)
              ·
                refine ⟨6305808990725542853745173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4203872660483695235830115 6305808990725542853745173)
                ·
                  refine ⟨295584796440259821269305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6305808990725542853745173 295584796440259821269305)
                  ·
                    rfl

theorem cell22_2590422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_2590422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2590422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2590422 prefixEnd_2590422 := by exact prefixLift 2590422
  have htrace : WordTrace (prefixWord ++ tailWord_2590422) baseStart_2590422 baseEnd_2590422 := by
    simpa [prefixWord, tailWord_2590422, baseEnd_2590422] using wordTrace_append hprefix tailTrace_2590422
  have hstable : (prefixWord ++ tailWord_2590422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590422).length < 2 ^ (prefixWord ++ tailWord_2590422).sum := by decide
  have hdescent : baseEnd_2590422 < baseStart_2590422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590452 : List Nat := [2, 6, 1, 1, 1, 2, 2, 1, 2, 4]
def baseStart_2590452 : Nat := 118140960795 + 2590452 * 2 ^ 59
def prefixEnd_2590452 : Nat := 4983230072969 + 3 ^ 40 * 2590452 * 2
def baseEnd_2590452 : Nat := 886764658933869385557823

theorem tailTrace_2590452 : CollatzResearch.WordTrace tailWord_2590452 prefixEnd_2590452 886764658933869385557823 := by
  unfold tailWord_2590452
  simp only [CollatzResearch.WordTrace]
  refine ⟨47240773205621146412166805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62987697607494861882889073 47240773205621146412166805)
  ·
    refine ⟨2214411244013491238070319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 47240773205621146412166805 2214411244013491238070319)
    ·
      refine ⟨3321616866020236857105479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2214411244013491238070319 3321616866020236857105479)
      ·
        refine ⟨4982425299030355285658219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3321616866020236857105479 4982425299030355285658219)
        ·
          refine ⟨7473637948545532928487329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4982425299030355285658219 7473637948545532928487329)
          ·
            refine ⟨5605228461409149696365497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7473637948545532928487329 5605228461409149696365497)
            ·
              refine ⟨4203921346056862272274123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5605228461409149696365497 4203921346056862272274123)
              ·
                refine ⟨6305882019085293408411185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4203921346056862272274123 6305882019085293408411185)
                ·
                  refine ⟨4729411514313970056308389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6305882019085293408411185 4729411514313970056308389)
                  ·
                    refine ⟨886764658933869385557823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4729411514313970056308389 886764658933869385557823)
                    ·
                      rfl

theorem cell22_2590452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_2590452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2590452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2590452 prefixEnd_2590452 := by exact prefixLift 2590452
  have htrace : WordTrace (prefixWord ++ tailWord_2590452) baseStart_2590452 baseEnd_2590452 := by
    simpa [prefixWord, tailWord_2590452, baseEnd_2590452] using wordTrace_append hprefix tailTrace_2590452
  have hstable : (prefixWord ++ tailWord_2590452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590452).length < 2 ^ (prefixWord ++ tailWord_2590452).sum := by decide
  have hdescent : baseEnd_2590452 < baseStart_2590452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590459 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 3, 7]
def baseStart_2590459 : Nat := 118140960795 + 2590459 * 2 ^ 59
def prefixEnd_2590459 : Nat := 4983230072969 + 3 ^ 40 * 2590459 * 2
def baseEnd_2590459 : Nat := 886767055176923700632801

theorem tailTrace_2590459 : CollatzResearch.WordTrace tailWord_2590459 prefixEnd_2590459 886767055176923700632801 := by
  unfold tailWord_2590459
  simp only [CollatzResearch.WordTrace]
  refine ⟨94481801722216933019838431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62987867814811288679892287 94481801722216933019838431)
  ·
    refine ⟨141722702583325399529757647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94481801722216933019838431 141722702583325399529757647)
    ·
      refine ⟨212584053874988099294636471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141722702583325399529757647 212584053874988099294636471)
      ·
        refine ⟨318876080812482148941954707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212584053874988099294636471 318876080812482148941954707)
        ·
          refine ⟨478314121218723223412932061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318876080812482148941954707 478314121218723223412932061)
          ·
            refine ⟨179367795457021208779849523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 478314121218723223412932061 179367795457021208779849523)
            ·
              refine ⟨269051693185531813169774285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179367795457021208779849523 269051693185531813169774285)
              ·
                refine ⟨100894384944574429938665357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 269051693185531813169774285 100894384944574429938665357)
                ·
                  refine ⟨37835394354215411226999509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100894384944574429938665357 37835394354215411226999509)
                  ·
                    refine ⟨886767055176923700632801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37835394354215411226999509 886767055176923700632801)
                    ·
                      rfl

theorem cell22_2590459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 7].length) (baseStart_2590459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2590459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2590459 prefixEnd_2590459 := by exact prefixLift 2590459
  have htrace : WordTrace (prefixWord ++ tailWord_2590459) baseStart_2590459 baseEnd_2590459 := by
    simpa [prefixWord, tailWord_2590459, baseEnd_2590459] using wordTrace_append hprefix tailTrace_2590459
  have hstable : (prefixWord ++ tailWord_2590459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590459).length < 2 ^ (prefixWord ++ tailWord_2590459).sum := by decide
  have hdescent : baseEnd_2590459 < baseStart_2590459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590484 : List Nat := [2, 4, 4, 1, 2, 1, 1, 7]
def baseStart_2590484 : Nat := 118140960795 + 2590484 * 2 ^ 59
def prefixEnd_2590484 : Nat := 4983230072969 + 3 ^ 40 * 2590484 * 2
def baseEnd_2590484 : Nat := 98530623687536885417525

theorem tailTrace_2590484 : CollatzResearch.WordTrace tailWord_2590484 prefixEnd_2590484 98530623687536885417525 := by
  unfold tailWord_2590484
  simp only [CollatzResearch.WordTrace]
  refine ⟨47241356773563181144749253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62988475698084241526332337 47241356773563181144749253)
  ·
    refine ⟨8857754395043096464640485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47241356773563181144749253 8857754395043096464640485)
    ·
      refine ⟨1660828949070580587120091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8857754395043096464640485 1660828949070580587120091)
      ·
        refine ⟨2491243423605870880680137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1660828949070580587120091 2491243423605870880680137)
        ·
          refine ⟨1868432567704403160510103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2491243423605870880680137 1868432567704403160510103)
          ·
            refine ⟨2802648851556604740765155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1868432567704403160510103 2802648851556604740765155)
            ·
              refine ⟨4203973277334907111147733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2802648851556604740765155 4203973277334907111147733)
              ·
                refine ⟨98530623687536885417525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4203973277334907111147733 98530623687536885417525)
                ·
                  rfl

theorem cell22_2590484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 7].length) (baseStart_2590484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2590484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2590484 prefixEnd_2590484 := by exact prefixLift 2590484
  have htrace : WordTrace (prefixWord ++ tailWord_2590484) baseStart_2590484 baseEnd_2590484 := by
    simpa [prefixWord, tailWord_2590484, baseEnd_2590484] using wordTrace_append hprefix tailTrace_2590484
  have hstable : (prefixWord ++ tailWord_2590484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590484).length < 2 ^ (prefixWord ++ tailWord_2590484).sum := by decide
  have hdescent : baseEnd_2590484 < baseStart_2590484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590525 : List Nat := [1, 4, 1, 4, 1, 2, 1, 3, 1, 4]
def baseStart_2590525 : Nat := 118140960795 + 2590525 * 2 ^ 59
def prefixEnd_2590525 : Nat := 4983230072969 + 3 ^ 40 * 2590525 * 2
def baseEnd_2590525 : Nat := 886789648325721528482599

theorem tailTrace_2590525 : CollatzResearch.WordTrace tailWord_2590525 prefixEnd_2590525 886789648325721528482599 := by
  unfold tailWord_2590525
  simp only [CollatzResearch.WordTrace]
  refine ⟨94484208939977826291741029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62989472626651884194494019 94484208939977826291741029)
  ·
    refine ⟨17715789176245842429701443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94484208939977826291741029 17715789176245842429701443)
    ·
      refine ⟨26573683764368763644552165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17715789176245842429701443 26573683764368763644552165)
      ·
        refine ⟨4982565705819143183353531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26573683764368763644552165 4982565705819143183353531)
        ·
          refine ⟨7473848558728714775030297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4982565705819143183353531 7473848558728714775030297)
          ·
            refine ⟨5605386419046536081272723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7473848558728714775030297 5605386419046536081272723)
            ·
              refine ⟨8408079628569804121909085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5605386419046536081272723 8408079628569804121909085)
              ·
                refine ⟨3153029860713676545715907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8408079628569804121909085 3153029860713676545715907)
                ·
                  refine ⟨4729544791070514818573861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3153029860713676545715907 4729544791070514818573861)
                  ·
                    refine ⟨886789648325721528482599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4729544791070514818573861 886789648325721528482599)
                    ·
                      rfl

theorem cell22_2590525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_2590525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2590525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2590525 prefixEnd_2590525 := by exact prefixLift 2590525
  have htrace : WordTrace (prefixWord ++ tailWord_2590525) baseStart_2590525 baseEnd_2590525 := by
    simpa [prefixWord, tailWord_2590525, baseEnd_2590525] using wordTrace_append hprefix tailTrace_2590525
  have hstable : (prefixWord ++ tailWord_2590525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590525).length < 2 ^ (prefixWord ++ tailWord_2590525).sum := by decide
  have hdescent : baseEnd_2590525 < baseStart_2590525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590538 : List Nat := [3, 1, 2, 1, 1, 1, 5, 1, 4, 3]
def baseStart_2590538 : Nat := 118140960795 + 2590538 * 2 ^ 59
def prefixEnd_2590538 : Nat := 4983230072969 + 3 ^ 40 * 2590538 * 2
def baseEnd_2590538 : Nat := 886794098491393827907559

theorem tailTrace_2590538 : CollatzResearch.WordTrace tailWord_2590538 prefixEnd_2590538 886794098491393827907559 := by
  unfold tailWord_2590538
  simp only [CollatzResearch.WordTrace]
  refine ⟨23621170772232682377991067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62989788725953819674642845 23621170772232682377991067)
  ·
    refine ⟨35431756158349023566986601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23621170772232682377991067 35431756158349023566986601)
    ·
      refine ⟨26573817118761767675239951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35431756158349023566986601 26573817118761767675239951)
      ·
        refine ⟨39860725678142651512859927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26573817118761767675239951 39860725678142651512859927)
        ·
          refine ⟨59791088517213977269289891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39860725678142651512859927 59791088517213977269289891)
          ·
            refine ⟨89686632775820965903934837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59791088517213977269289891 89686632775820965903934837)
            ·
              refine ⟨8408121822733215553493891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89686632775820965903934837 8408121822733215553493891)
              ·
                refine ⟨12612182734099823330240837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8408121822733215553493891 12612182734099823330240837)
                ·
                  refine ⟨2364784262643716874420157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12612182734099823330240837 2364784262643716874420157)
                  ·
                    refine ⟨886794098491393827907559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2364784262643716874420157 886794098491393827907559)
                    ·
                      rfl

theorem cell22_2590538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 4, 3].length) (baseStart_2590538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2590538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2590538 prefixEnd_2590538 := by exact prefixLift 2590538
  have htrace : WordTrace (prefixWord ++ tailWord_2590538) baseStart_2590538 baseEnd_2590538 := by
    simpa [prefixWord, tailWord_2590538, baseEnd_2590538] using wordTrace_append hprefix tailTrace_2590538
  have hstable : (prefixWord ++ tailWord_2590538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590538).length < 2 ^ (prefixWord ++ tailWord_2590538).sum := by decide
  have hdescent : baseEnd_2590538 < baseStart_2590538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590606 : List Nat := [4, 1, 1, 5, 1, 2, 2, 1, 2, 3]
def baseStart_2590606 : Nat := 118140960795 + 2590606 * 2 ^ 59
def prefixEnd_2590606 : Nat := 4983230072969 + 3 ^ 40 * 2590606 * 2
def baseEnd_2590606 : Nat := 886817376281064317207351

theorem tailTrace_2590606 : CollatzResearch.WordTrace tailWord_2590606 prefixEnd_2590606 886817376281064317207351 := by
  unfold tailWord_2590606
  simp only [CollatzResearch.WordTrace]
  refine ⟨11810895406585547140679959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62991442168456251416959781 11810895406585547140679959)
  ·
    refine ⟨17716343109878320711019939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11810895406585547140679959 17716343109878320711019939)
    ·
      refine ⟨26574514664817481066529909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17716343109878320711019939 26574514664817481066529909)
      ·
        refine ⟨2491360749826638849987179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26574514664817481066529909 2491360749826638849987179)
        ·
          refine ⟨3737041124739958274980769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2491360749826638849987179 3737041124739958274980769)
          ·
            refine ⟨2802780843554968706235577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3737041124739958274980769 2802780843554968706235577)
            ·
              refine ⟨2102085632666226529676683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2802780843554968706235577 2102085632666226529676683)
              ·
                refine ⟨3153128448999339794515025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2102085632666226529676683 3153128448999339794515025)
                ·
                  refine ⟨2364846336749504845886269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3153128448999339794515025 2364846336749504845886269)
                  ·
                    refine ⟨886817376281064317207351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2364846336749504845886269 886817376281064317207351)
                    ·
                      rfl

theorem cell22_2590606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 1, 2, 3].length) (baseStart_2590606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2590606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2590606 prefixEnd_2590606 := by exact prefixLift 2590606
  have htrace : WordTrace (prefixWord ++ tailWord_2590606) baseStart_2590606 baseEnd_2590606 := by
    simpa [prefixWord, tailWord_2590606, baseEnd_2590606] using wordTrace_append hprefix tailTrace_2590606
  have hstable : (prefixWord ++ tailWord_2590606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590606).length < 2 ^ (prefixWord ++ tailWord_2590606).sum := by decide
  have hdescent : baseEnd_2590606 < baseStart_2590606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590611 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 6, 5]
def baseStart_2590611 : Nat := 118140960795 + 2590611 * 2 ^ 59
def prefixEnd_2590611 : Nat := 4983230072969 + 3 ^ 40 * 2590611 * 2
def baseEnd_2590611 : Nat := 886819087883245970832335

theorem tailTrace_2590611 : CollatzResearch.WordTrace tailWord_2590611 prefixEnd_2590611 886819087883245970832335 := by
  unfold tailWord_2590611
  simp only [CollatzResearch.WordTrace]
  refine ⟨94487345617666262979371687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62991563745110841986247791 94487345617666262979371687)
  ·
    refine ⟨141731018426499394469057531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94487345617666262979371687 141731018426499394469057531)
    ·
      refine ⟨212596527639749091703586297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141731018426499394469057531 212596527639749091703586297)
      ·
        refine ⟨159447395729811818777689723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212596527639749091703586297 159447395729811818777689723)
        ·
          refine ⟨239171093594717728166534585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159447395729811818777689723 239171093594717728166534585)
          ·
            refine ⟨179378320196038296124900939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 239171093594717728166534585 179378320196038296124900939)
            ·
              refine ⟨269067480294057444187351409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179378320196038296124900939 269067480294057444187351409)
              ·
                refine ⟨201800610220543083140513557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 269067480294057444187351409 201800610220543083140513557)
                ·
                  refine ⟨9459403604087957022211573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 201800610220543083140513557 9459403604087957022211573)
                  ·
                    refine ⟨886819087883245970832335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9459403604087957022211573 886819087883245970832335)
                    ·
                      rfl

theorem cell22_2590611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 5].length) (baseStart_2590611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2590611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2590611 prefixEnd_2590611 := by exact prefixLift 2590611
  have htrace : WordTrace (prefixWord ++ tailWord_2590611) baseStart_2590611 baseEnd_2590611 := by
    simpa [prefixWord, tailWord_2590611, baseEnd_2590611] using wordTrace_append hprefix tailTrace_2590611
  have hstable : (prefixWord ++ tailWord_2590611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590611).length < 2 ^ (prefixWord ++ tailWord_2590611).sum := by decide
  have hdescent : baseEnd_2590611 < baseStart_2590611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590613 : List Nat := [1, 3, 2, 1, 1, 3, 3, 3, 5]
def baseStart_2590613 : Nat := 118140960795 + 2590613 * 2 ^ 59
def prefixEnd_2590613 : Nat := 4983230072969 + 3 ^ 40 * 2590613 * 2
def baseEnd_2590613 : Nat := 295606590841372877427443

theorem tailTrace_2590613 : CollatzResearch.WordTrace tailWord_2590613 prefixEnd_2590613 295606590841372877427443 := by
  unfold tailWord_2590613
  simp only [CollatzResearch.WordTrace]
  refine ⟨94487418563659017320944493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62991612375772678213962995 94487418563659017320944493)
  ·
    refine ⟨35432781961372131495354185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94487418563659017320944493 35432781961372131495354185)
    ·
      refine ⟨26574586471029098621515639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35432781961372131495354185 26574586471029098621515639)
      ·
        refine ⟨39861879706543647932273459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26574586471029098621515639 39861879706543647932273459)
        ·
          refine ⟨59792819559815471898410189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39861879706543647932273459 59792819559815471898410189)
          ·
            refine ⟨22422307334930801961903821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59792819559815471898410189 22422307334930801961903821)
            ·
              refine ⟨8408365250599050735713933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22422307334930801961903821 8408365250599050735713933)
              ·
                refine ⟨3153136968974644025892725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8408365250599050735713933 3153136968974644025892725)
                ·
                  refine ⟨295606590841372877427443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3153136968974644025892725 295606590841372877427443)
                  ·
                    rfl

theorem cell22_2590613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 3, 5].length) (baseStart_2590613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2590613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2590613 prefixEnd_2590613 := by exact prefixLift 2590613
  have htrace : WordTrace (prefixWord ++ tailWord_2590613) baseStart_2590613 baseEnd_2590613 := by
    simpa [prefixWord, tailWord_2590613, baseEnd_2590613] using wordTrace_append hprefix tailTrace_2590613
  have hstable : (prefixWord ++ tailWord_2590613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590613).length < 2 ^ (prefixWord ++ tailWord_2590613).sum := by decide
  have hdescent : baseEnd_2590613 < baseStart_2590613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590724 : List Nat := [2, 3, 2, 4, 1, 2, 1, 1, 1, 5]
def baseStart_2590724 : Nat := 118140960795 + 2590724 * 2 ^ 59
def prefixEnd_2590724 : Nat := 4983230072969 + 3 ^ 40 * 2590724 * 2
def baseEnd_2590724 : Nat := 886857770092551342756989

theorem tailTrace_2590724 : CollatzResearch.WordTrace tailWord_2590724 prefixEnd_2590724 886857770092551342756989 := by
  unfold tailWord_2590724
  simp only [CollatzResearch.WordTrace]
  refine ⟨47245733533128441639117613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62994311377504588852156817 47245733533128441639117613)
  ·
    refine ⟨17717150074923165614669105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47245733533128441639117613 17717150074923165614669105)
    ·
      refine ⟨13287862556192374211001829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17717150074923165614669105 13287862556192374211001829)
      ·
        refine ⟨2491474229286070164562843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13287862556192374211001829 2491474229286070164562843)
        ·
          refine ⟨3737211343929105246844265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2491474229286070164562843 3737211343929105246844265)
          ·
            refine ⟨2802908507946828935133199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3737211343929105246844265 2802908507946828935133199)
            ·
              refine ⟨4204362761920243402699799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2802908507946828935133199 4204362761920243402699799)
              ·
                refine ⟨6306544142880365104049699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4204362761920243402699799 6306544142880365104049699)
                ·
                  refine ⟨9459816214320547656074549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6306544142880365104049699 9459816214320547656074549)
                  ·
                    refine ⟨886857770092551342756989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9459816214320547656074549 886857770092551342756989)
                    ·
                      rfl

theorem cell22_2590724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_2590724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2590724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2590724 prefixEnd_2590724 := by exact prefixLift 2590724
  have htrace : WordTrace (prefixWord ++ tailWord_2590724) baseStart_2590724 baseEnd_2590724 := by
    simpa [prefixWord, tailWord_2590724, baseEnd_2590724] using wordTrace_append hprefix tailTrace_2590724
  have hstable : (prefixWord ++ tailWord_2590724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590724).length < 2 ^ (prefixWord ++ tailWord_2590724).sum := by decide
  have hdescent : baseEnd_2590724 < baseStart_2590724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590763 : List Nat := [1, 1, 1, 1, 2, 1, 4, 4, 2, 5]
def baseStart_2590763 : Nat := 118140960795 + 2590763 * 2 ^ 59
def prefixEnd_2590763 : Nat := 4983230072969 + 3 ^ 40 * 2590763 * 2
def baseEnd_2590763 : Nat := 886871120589568241031869

theorem tailTrace_2590763 : CollatzResearch.WordTrace tailWord_2590763 prefixEnd_2590763 886871120589568241031869 := by
  unfold tailWord_2590763
  simp only [CollatzResearch.WordTrace]
  refine ⟨94492889513115592938904943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62995259675410395292603295 94492889513115592938904943)
  ·
    refine ⟨141739334269673389408357415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94492889513115592938904943 141739334269673389408357415)
    ·
      refine ⟨212609001404510084112536123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141739334269673389408357415 212609001404510084112536123)
      ·
        refine ⟨318913502106765126168804185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212609001404510084112536123 318913502106765126168804185)
        ·
          refine ⟨239185126580073844626603139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 318913502106765126168804185 239185126580073844626603139)
          ·
            refine ⟨358777689870110766939904709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239185126580073844626603139 358777689870110766939904709)
            ·
              refine ⟨67270816850645768801232133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 358777689870110766939904709 67270816850645768801232133)
              ·
                refine ⟨12613278159496081650231025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67270816850645768801232133 12613278159496081650231025)
                ·
                  refine ⟨9459958619622061237673269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12613278159496081650231025 9459958619622061237673269)
                  ·
                    refine ⟨886871120589568241031869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9459958619622061237673269 886871120589568241031869)
                    ·
                      rfl

theorem cell22_2590763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 5].length) (baseStart_2590763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2590763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2590763 prefixEnd_2590763 := by exact prefixLift 2590763
  have htrace : WordTrace (prefixWord ++ tailWord_2590763) baseStart_2590763 baseEnd_2590763 := by
    simpa [prefixWord, tailWord_2590763, baseEnd_2590763] using wordTrace_append hprefix tailTrace_2590763
  have hstable : (prefixWord ++ tailWord_2590763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590763).length < 2 ^ (prefixWord ++ tailWord_2590763).sum := by decide
  have hdescent : baseEnd_2590763 < baseStart_2590763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590778 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 2, 8]
def baseStart_2590778 : Nat := 118140960795 + 2590778 * 2 ^ 59
def prefixEnd_2590778 : Nat := 4983230072969 + 3 ^ 40 * 2590778 * 2
def baseEnd_2590778 : Nat := 886876255396113201906823

theorem tailTrace_2590778 : CollatzResearch.WordTrace tailWord_2590778 prefixEnd_2590778 886876255396113201906823 := by
  unfold tailWord_2590778
  simp only [CollatzResearch.WordTrace]
  refine ⟨23623359152015312625175247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62995624405374167000467325 23623359152015312625175247)
  ·
    refine ⟨35435038728022968937762871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23623359152015312625175247 35435038728022968937762871)
    ·
      refine ⟨53152558092034453406644307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35435038728022968937762871 53152558092034453406644307)
      ·
        refine ⟨79728837138051680109966461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53152558092034453406644307 79728837138051680109966461)
        ·
          refine ⟨29898313926769380041237423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79728837138051680109966461 29898313926769380041237423)
          ·
            refine ⟨44847470890154070061856135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29898313926769380041237423 44847470890154070061856135)
            ·
              refine ⟨67271206335231105092784203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44847470890154070061856135 67271206335231105092784203)
              ·
                refine ⟨100906809502846657639176305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67271206335231105092784203 100906809502846657639176305)
                ·
                  refine ⟨75680107127134993229382229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100906809502846657639176305 75680107127134993229382229)
                  ·
                    refine ⟨886876255396113201906823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 75680107127134993229382229 886876255396113201906823)
                    ·
                      rfl

theorem cell22_2590778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_2590778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2590778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2590778 prefixEnd_2590778 := by exact prefixLift 2590778
  have htrace : WordTrace (prefixWord ++ tailWord_2590778) baseStart_2590778 baseEnd_2590778 := by
    simpa [prefixWord, tailWord_2590778, baseEnd_2590778] using wordTrace_append hprefix tailTrace_2590778
  have hstable : (prefixWord ++ tailWord_2590778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590778).length < 2 ^ (prefixWord ++ tailWord_2590778).sum := by decide
  have hdescent : baseEnd_2590778 < baseStart_2590778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590793 : List Nat := [1, 2, 1, 1, 2, 2, 4, 1, 8]
def baseStart_2590793 : Nat := 118140960795 + 2590793 * 2 ^ 59
def prefixEnd_2590793 : Nat := 4983230072969 + 3 ^ 40 * 2590793 * 2
def baseEnd_2590793 : Nat := 295627130067552720927259

theorem tailTrace_2590793 : CollatzResearch.WordTrace tailWord_2590793 prefixEnd_2590793 295627130067552720927259 := by
  unfold tailWord_2590793
  simp only [CollatzResearch.WordTrace]
  refine ⟨94493983703006908062497033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62995989135337938708331355 94493983703006908062497033)
  ·
    refine ⟨70870487777255181046872775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94493983703006908062497033 70870487777255181046872775)
    ·
      refine ⟨106305731665882771570309163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70870487777255181046872775 106305731665882771570309163)
      ·
        refine ⟨159458597498824157355463745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106305731665882771570309163 159458597498824157355463745)
        ·
          refine ⟨119593948124118118016597809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159458597498824157355463745 119593948124118118016597809)
          ·
            refine ⟨89695461093088588512448357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119593948124118118016597809 89695461093088588512448357)
            ·
              refine ⟨16817898954954110346084067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89695461093088588512448357 16817898954954110346084067)
              ·
                refine ⟨25226848432431165519126101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16817898954954110346084067 25226848432431165519126101)
                ·
                  refine ⟨295627130067552720927259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25226848432431165519126101 295627130067552720927259)
                  ·
                    rfl

theorem cell22_2590793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 8].length) (baseStart_2590793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2590793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2590793 prefixEnd_2590793 := by exact prefixLift 2590793
  have htrace : WordTrace (prefixWord ++ tailWord_2590793) baseStart_2590793 baseEnd_2590793 := by
    simpa [prefixWord, tailWord_2590793, baseEnd_2590793] using wordTrace_append hprefix tailTrace_2590793
  have hstable : (prefixWord ++ tailWord_2590793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590793).length < 2 ^ (prefixWord ++ tailWord_2590793).sum := by decide
  have hdescent : baseEnd_2590793 < baseStart_2590793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590934 : List Nat := [5, 2, 1, 2, 1, 1, 2, 1, 7]
def baseStart_2590934 : Nat := 118140960795 + 2590934 * 2 ^ 59
def prefixEnd_2590934 : Nat := 4983230072969 + 3 ^ 40 * 2590934 * 2
def baseEnd_2590934 : Nat := 295643219128060265002115

theorem tailTrace_2590934 : CollatzResearch.WordTrace tailWord_2590934 prefixEnd_2590934 295643219128060265002115 := by
  unfold tailWord_2590934
  simp only [CollatzResearch.WordTrace]
  refine ⟨5906195399718505571461241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62999417596997392762253237 5906195399718505571461241)
  ·
    refine ⟨4429646549788879178595931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5906195399718505571461241 4429646549788879178595931)
    ·
      refine ⟨6644469824683318767893897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4429646549788879178595931 6644469824683318767893897)
      ·
        refine ⟨4983352368512489075920423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6644469824683318767893897 4983352368512489075920423)
        ·
          refine ⟨7475028552768733613880635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4983352368512489075920423 7475028552768733613880635)
          ·
            refine ⟨11212542829153100420820953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7475028552768733613880635 11212542829153100420820953)
            ·
              refine ⟨8409407121864825315615715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11212542829153100420820953 8409407121864825315615715)
              ·
                refine ⟨12614110682797237973423573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8409407121864825315615715 12614110682797237973423573)
                ·
                  refine ⟨295643219128060265002115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12614110682797237973423573 295643219128060265002115)
                  ·
                    rfl

theorem cell22_2590934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_2590934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2590934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2590934 prefixEnd_2590934 := by exact prefixLift 2590934
  have htrace : WordTrace (prefixWord ++ tailWord_2590934) baseStart_2590934 baseEnd_2590934 := by
    simpa [prefixWord, tailWord_2590934, baseEnd_2590934] using wordTrace_append hprefix tailTrace_2590934
  have hstable : (prefixWord ++ tailWord_2590934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590934).length < 2 ^ (prefixWord ++ tailWord_2590934).sum := by decide
  have hdescent : baseEnd_2590934 < baseStart_2590934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590951 : List Nat := [1, 1, 5, 3, 1, 3, 2, 1, 5]
def baseStart_2590951 : Nat := 118140960795 + 2590951 * 2 ^ 59
def prefixEnd_2590951 : Nat := 4983230072969 + 3 ^ 40 * 2590951 * 2
def baseEnd_2590951 : Nat := 295645158943866139110431

theorem tailTrace_2590951 : CollatzResearch.WordTrace tailWord_2590951 prefixEnd_2590951 295645158943866139110431 := by
  unfold tailWord_2590951
  simp only [CollatzResearch.WordTrace]
  refine ⟨94499746436434501046748707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62999830957623000697832471 94499746436434501046748707)
  ·
    refine ⟨141749619654651751570123061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94499746436434501046748707 141749619654651751570123061)
    ·
      refine ⟨13289026842623601709699037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 141749619654651751570123061 13289026842623601709699037)
      ·
        refine ⟨4983385065983850641137139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13289026842623601709699037 4983385065983850641137139)
        ·
          refine ⟨7475077598975775961705709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4983385065983850641137139 7475077598975775961705709)
          ·
            refine ⟨2803154099615915985639641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7475077598975775961705709 2803154099615915985639641)
            ·
              refine ⟨2102365574711936989229731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2803154099615915985639641 2102365574711936989229731)
              ·
                refine ⟨3153548362067905483844597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2102365574711936989229731 3153548362067905483844597)
                ·
                  refine ⟨295645158943866139110431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3153548362067905483844597 295645158943866139110431)
                  ·
                    rfl

theorem cell22_2590951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 1, 5].length) (baseStart_2590951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2590951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2590951 prefixEnd_2590951 := by exact prefixLift 2590951
  have htrace : WordTrace (prefixWord ++ tailWord_2590951) baseStart_2590951 baseEnd_2590951 := by
    simpa [prefixWord, tailWord_2590951, baseEnd_2590951] using wordTrace_append hprefix tailTrace_2590951
  have hstable : (prefixWord ++ tailWord_2590951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590951).length < 2 ^ (prefixWord ++ tailWord_2590951).sum := by decide
  have hdescent : baseEnd_2590951 < baseStart_2590951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590960 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 5, 5]
def baseStart_2590960 : Nat := 118140960795 + 2590960 * 2 ^ 59
def prefixEnd_2590960 : Nat := 4983230072969 + 3 ^ 40 * 2590960 * 2
def baseEnd_2590960 : Nat := 886938557715525393856265

theorem tailTrace_2590960 : CollatzResearch.WordTrace tailWord_2590960 prefixEnd_2590960 886938557715525393856265 := by
  unfold tailWord_2590960
  simp only [CollatzResearch.WordTrace]
  refine ⟨47250037346700947791913167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63000049795601263722550889 47250037346700947791913167)
  ·
    refine ⟨70875056020051421687869751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47250037346700947791913167 70875056020051421687869751)
    ·
      refine ⟨106312584030077132531804627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70875056020051421687869751 106312584030077132531804627)
      ·
        refine ⟨159468876045115698797706941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106312584030077132531804627 159468876045115698797706941)
        ·
          refine ⟨59800828516918387049140103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159468876045115698797706941 59800828516918387049140103)
          ·
            refine ⟨89701242775377580573710155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59800828516918387049140103 89701242775377580573710155)
            ·
              refine ⟨134551864163066370860565233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89701242775377580573710155 134551864163066370860565233)
              ·
                refine ⟨100913898122299778145423925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134551864163066370860565233 100913898122299778145423925)
                ·
                  refine ⟨9460677948965604201133493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 100913898122299778145423925 9460677948965604201133493)
                  ·
                    refine ⟨886938557715525393856265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9460677948965604201133493 886938557715525393856265)
                    ·
                      rfl

theorem cell22_2590960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 5, 5].length) (baseStart_2590960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2590960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2590960 prefixEnd_2590960 := by exact prefixLift 2590960
  have htrace : WordTrace (prefixWord ++ tailWord_2590960) baseStart_2590960 baseEnd_2590960 := by
    simpa [prefixWord, tailWord_2590960, baseEnd_2590960] using wordTrace_append hprefix tailTrace_2590960
  have hstable : (prefixWord ++ tailWord_2590960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590960).length < 2 ^ (prefixWord ++ tailWord_2590960).sum := by decide
  have hdescent : baseEnd_2590960 < baseStart_2590960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590977 : List Nat := [1, 2, 4, 1, 1, 2, 3, 2, 1, 5]
def baseStart_2590977 : Nat := 118140960795 + 2590977 * 2 ^ 59
def prefixEnd_2590977 : Nat := 4983230072969 + 3 ^ 40 * 2590977 * 2
def baseEnd_2590977 : Nat := 886944377162943016181213

theorem tailTrace_2590977 : CollatzResearch.WordTrace tailWord_2590977 prefixEnd_2590977 886944377162943016181213 := by
  unfold tailWord_2590977
  simp only [CollatzResearch.WordTrace]
  refine ⟨94500694734340307487195185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63000463156226871658130123 94500694734340307487195185)
  ·
    refine ⟨70875521050755230615396389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94500694734340307487195185 70875521050755230615396389)
    ·
      refine ⟨13289160197016605740386823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70875521050755230615396389 13289160197016605740386823)
      ·
        refine ⟨19933740295524908610580235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13289160197016605740386823 19933740295524908610580235)
        ·
          refine ⟨29900610443287362915870353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19933740295524908610580235 29900610443287362915870353)
          ·
            refine ⟨22425457832465522186902765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29900610443287362915870353 22425457832465522186902765)
            ·
              refine ⟨8409546687174570820088537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22425457832465522186902765 8409546687174570820088537)
              ·
                refine ⟨6307160015380928115066403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8409546687174570820088537 6307160015380928115066403)
                ·
                  refine ⟨9460740023071392172599605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6307160015380928115066403 9460740023071392172599605)
                  ·
                    refine ⟨886944377162943016181213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9460740023071392172599605 886944377162943016181213)
                    ·
                      rfl

theorem cell22_2590977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_2590977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2590977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2590977 prefixEnd_2590977 := by exact prefixLift 2590977
  have htrace : WordTrace (prefixWord ++ tailWord_2590977) baseStart_2590977 baseEnd_2590977 := by
    simpa [prefixWord, tailWord_2590977, baseEnd_2590977] using wordTrace_append hprefix tailTrace_2590977
  have hstable : (prefixWord ++ tailWord_2590977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590977).length < 2 ^ (prefixWord ++ tailWord_2590977).sum := by decide
  have hdescent : baseEnd_2590977 < baseStart_2590977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591007 : List Nat := [1, 1, 2, 4, 3, 1, 3, 7]
def baseStart_2591007 : Nat := 118140960795 + 2591007 * 2 ^ 59
def prefixEnd_2591007 : Nat := 4983230072969 + 3 ^ 40 * 2591007 * 2
def baseEnd_2591007 : Nat := 98550516308448104214569

theorem tailTrace_2591007 : CollatzResearch.WordTrace tailWord_2591007 prefixEnd_2591007 98550516308448104214569 := by
  unfold tailWord_2591007
  simp only [CollatzResearch.WordTrace]
  refine ⟨94501788924231622610787275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63001192616154415073858183 94501788924231622610787275)
  ·
    refine ⟨141752683386347433916180913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94501788924231622610787275 141752683386347433916180913)
    ·
      refine ⟨106314512539760575437135685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141752683386347433916180913 106314512539760575437135685)
      ·
        refine ⟨19933971101205107894462941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106314512539760575437135685 19933971101205107894462941)
        ·
          refine ⟨7475239162951915460423603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19933971101205107894462941 7475239162951915460423603)
          ·
            refine ⟨11212858744427873190635405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7475239162951915460423603 11212858744427873190635405)
            ·
              refine ⟨4204822029160452446488277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11212858744427873190635405 4204822029160452446488277)
              ·
                refine ⟨98550516308448104214569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4204822029160452446488277 98550516308448104214569)
                ·
                  rfl

theorem cell22_2591007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 7].length) (baseStart_2591007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2591007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2591007 prefixEnd_2591007 := by exact prefixLift 2591007
  have htrace : WordTrace (prefixWord ++ tailWord_2591007) baseStart_2591007 baseEnd_2591007 := by
    simpa [prefixWord, tailWord_2591007, baseEnd_2591007] using wordTrace_append hprefix tailTrace_2591007
  have hstable : (prefixWord ++ tailWord_2591007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591007).length < 2 ^ (prefixWord ++ tailWord_2591007).sum := by decide
  have hdescent : baseEnd_2591007 < baseStart_2591007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591026 : List Nat := [3, 2, 1, 1, 5, 2, 1, 1, 2, 4]
def baseStart_2591026 : Nat := 118140960795 + 2591026 * 2 ^ 59
def prefixEnd_2591026 : Nat := 4983230072969 + 3 ^ 40 * 2591026 * 2
def baseEnd_2591026 : Nat := 886961150864323221706063

theorem tailTrace_2591026 : CollatzResearch.WordTrace tailWord_2591026 prefixEnd_2591026 886961150864323221706063 := by
  unfold tailWord_2591026
  simp only [CollatzResearch.WordTrace]
  refine ⟨23625620477790697213932233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63001654607441859237152621 23625620477790697213932233)
  ·
    refine ⟨17719215358343022910449175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23625620477790697213932233 17719215358343022910449175)
    ·
      refine ⟨26578823037514534365673763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17719215358343022910449175 26578823037514534365673763)
      ·
        refine ⟨39868234556271801548510645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26578823037514534365673763 39868234556271801548510645)
        ·
          refine ⟨3737646989650481395172873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39868234556271801548510645 3737646989650481395172873)
          ·
            refine ⟨2803235242237861046379655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3737646989650481395172873 2803235242237861046379655)
            ·
              refine ⟨4204852863356791569569483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2803235242237861046379655 4204852863356791569569483)
              ·
                refine ⟨6307279295035187354354225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4204852863356791569569483 6307279295035187354354225)
                ·
                  refine ⟨4730459471276390515765669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6307279295035187354354225 4730459471276390515765669)
                  ·
                    refine ⟨886961150864323221706063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4730459471276390515765669 886961150864323221706063)
                    ·
                      rfl

theorem cell22_2591026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 2, 4].length) (baseStart_2591026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2591026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2591026 prefixEnd_2591026 := by exact prefixLift 2591026
  have htrace : WordTrace (prefixWord ++ tailWord_2591026) baseStart_2591026 baseEnd_2591026 := by
    simpa [prefixWord, tailWord_2591026, baseEnd_2591026] using wordTrace_append hprefix tailTrace_2591026
  have hstable : (prefixWord ++ tailWord_2591026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591026).length < 2 ^ (prefixWord ++ tailWord_2591026).sum := by decide
  have hdescent : baseEnd_2591026 < baseStart_2591026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591052 : List Nat := [2, 2, 1, 3, 2, 1, 3, 1, 7]
def baseStart_2591052 : Nat := 118140960795 + 2591052 * 2 ^ 59
def prefixEnd_2591052 : Nat := 4983230072969 + 3 ^ 40 * 2591052 * 2
def baseEnd_2591052 : Nat := 295656683731889273518661

theorem tailTrace_2591052 : CollatzResearch.WordTrace tailWord_2591052 prefixEnd_2591052 295656683731889273518661 := by
  unfold tailWord_2591052
  simp only [CollatzResearch.WordTrace]
  refine ⟨47251715104534297648087705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63002286806045730197450273 47251715104534297648087705)
  ·
    refine ⟨35438786328400723236065779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47251715104534297648087705 35438786328400723236065779)
    ·
      refine ⟨53158179492601084854098669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35438786328400723236065779 53158179492601084854098669)
      ·
        refine ⟨19934317309725406820287001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53158179492601084854098669 19934317309725406820287001)
        ·
          refine ⟨14950737982294055115215251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19934317309725406820287001 14950737982294055115215251)
          ·
            refine ⟨22426106973441082672822877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14950737982294055115215251 22426106973441082672822877)
            ·
              refine ⟨8409790115040406002308579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22426106973441082672822877 8409790115040406002308579)
              ·
                refine ⟨12614685172560609003462869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8409790115040406002308579 12614685172560609003462869)
                ·
                  refine ⟨295656683731889273518661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12614685172560609003462869 295656683731889273518661)
                  ·
                    rfl

theorem cell22_2591052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 7].length) (baseStart_2591052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2591052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2591052 prefixEnd_2591052 := by exact prefixLift 2591052
  have htrace : WordTrace (prefixWord ++ tailWord_2591052) baseStart_2591052 baseEnd_2591052 := by
    simpa [prefixWord, tailWord_2591052, baseEnd_2591052] using wordTrace_append hprefix tailTrace_2591052
  have hstable : (prefixWord ++ tailWord_2591052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591052).length < 2 ^ (prefixWord ++ tailWord_2591052).sum := by decide
  have hdescent : baseEnd_2591052 < baseStart_2591052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591056 : List Nat := [2, 1, 1, 1, 1, 6, 2, 4, 1, 3]
def baseStart_2591056 : Nat := 118140960795 + 2591056 * 2 ^ 59
def prefixEnd_2591056 : Nat := 4983230072969 + 3 ^ 40 * 2591056 * 2
def baseEnd_2591056 : Nat := 886971420477413143455971

theorem tailTrace_2591056 : CollatzResearch.WordTrace tailWord_2591056 prefixEnd_2591056 886971420477413143455971 := by
  unfold tailWord_2591056
  simp only [CollatzResearch.WordTrace]
  refine ⟨47251788050527051989660511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63002384067369402652880681 47251788050527051989660511)
  ·
    refine ⟨70877682075790577984490767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47251788050527051989660511 70877682075790577984490767)
    ·
      refine ⟨106316523113685866976736151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70877682075790577984490767 106316523113685866976736151)
      ·
        refine ⟨159474784670528800465104227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106316523113685866976736151 159474784670528800465104227)
        ·
          refine ⟨239212177005793200697656341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159474784670528800465104227 239212177005793200697656341)
          ·
            refine ⟨11213070797146556282702641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 239212177005793200697656341 11213070797146556282702641)
            ·
              refine ⟨8409803097859917212026981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11213070797146556282702641 8409803097859917212026981)
              ·
                refine ⟨1576838080848734477255059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8409803097859917212026981 1576838080848734477255059)
                ·
                  refine ⟨2365257121273101715882589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1576838080848734477255059 2365257121273101715882589)
                  ·
                    refine ⟨886971420477413143455971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2365257121273101715882589 886971420477413143455971)
                    ·
                      rfl

theorem cell22_2591056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 4, 1, 3].length) (baseStart_2591056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2591056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2591056 prefixEnd_2591056 := by exact prefixLift 2591056
  have htrace : WordTrace (prefixWord ++ tailWord_2591056) baseStart_2591056 baseEnd_2591056 := by
    simpa [prefixWord, tailWord_2591056, baseEnd_2591056] using wordTrace_append hprefix tailTrace_2591056
  have hstable : (prefixWord ++ tailWord_2591056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591056).length < 2 ^ (prefixWord ++ tailWord_2591056).sum := by decide
  have hdescent : baseEnd_2591056 < baseStart_2591056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591099 : List Nat := [1, 1, 1, 1, 1, 7, 2, 3, 1, 4]
def baseStart_2591099 : Nat := 118140960795 + 2591099 * 2 ^ 59
def prefixEnd_2591099 : Nat := 4983230072969 + 3 ^ 40 * 2591099 * 2
def baseEnd_2591099 : Nat := 886986140256175364630839

theorem tailTrace_2591099 : CollatzResearch.WordTrace tailWord_2591099 prefixEnd_2591099 886986140256175364630839 := by
  unfold tailWord_2591099
  simp only [CollatzResearch.WordTrace]
  refine ⟨94505144439898322323136351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63003429626598881548757567 94505144439898322323136351)
  ·
    refine ⟨141757716659847483484704527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94505144439898322323136351 141757716659847483484704527)
    ·
      refine ⟨212636574989771225227056791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141757716659847483484704527 212636574989771225227056791)
      ·
        refine ⟨318954862484656837840585187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212636574989771225227056791 318954862484656837840585187)
        ·
          refine ⟨478432293726985256760877781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318954862484656837840585187 478432293726985256760877781)
          ·
            refine ⟨11213256884226216955333073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 478432293726985256760877781 11213256884226216955333073)
            ·
              refine ⟨8409942663169662716499805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11213256884226216955333073 8409942663169662716499805)
              ·
                refine ⟨3153728498688623518687427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8409942663169662716499805 3153728498688623518687427)
                ·
                  refine ⟨4730592748032935278031141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3153728498688623518687427 4730592748032935278031141)
                  ·
                    refine ⟨886986140256175364630839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4730592748032935278031141 886986140256175364630839)
                    ·
                      rfl

theorem cell22_2591099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 3, 1, 4].length) (baseStart_2591099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2591099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2591099 prefixEnd_2591099 := by exact prefixLift 2591099
  have htrace : WordTrace (prefixWord ++ tailWord_2591099) baseStart_2591099 baseEnd_2591099 := by
    simpa [prefixWord, tailWord_2591099, baseEnd_2591099] using wordTrace_append hprefix tailTrace_2591099
  have hstable : (prefixWord ++ tailWord_2591099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591099).length < 2 ^ (prefixWord ++ tailWord_2591099).sum := by decide
  have hdescent : baseEnd_2591099 < baseStart_2591099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591127 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 3, 6]
def baseStart_2591127 : Nat := 118140960795 + 2591127 * 2 ^ 59
def prefixEnd_2591127 : Nat := 4983230072969 + 3 ^ 40 * 2591127 * 2
def baseEnd_2591127 : Nat := 886995725228392624930753

theorem tailTrace_2591127 : CollatzResearch.WordTrace tailWord_2591127 prefixEnd_2591127 886995725228392624930753 := by
  unfold tailWord_2591127
  simp only [CollatzResearch.WordTrace]
  refine ⟨94506165683796883105155635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63004110455864588736770423 94506165683796883105155635)
  ·
    refine ⟨141759248525695324657733453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94506165683796883105155635 141759248525695324657733453)
    ·
      refine ⟨53159718197135746746650045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141759248525695324657733453 53159718197135746746650045)
      ·
        refine ⟨19934894323925905029993767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53159718197135746746650045 19934894323925905029993767)
        ·
          refine ⟨29902341485888857544990651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19934894323925905029993767 29902341485888857544990651)
          ·
            refine ⟨44853512228833286317485977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29902341485888857544990651 44853512228833286317485977)
            ·
              refine ⟨33640134171624964738114483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44853512228833286317485977 33640134171624964738114483)
              ·
                refine ⟨50460201257437447107171725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33640134171624964738114483 50460201257437447107171725)
                ·
                  refine ⟨18922575471539042665189397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50460201257437447107171725 18922575471539042665189397)
                  ·
                    refine ⟨886995725228392624930753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18922575471539042665189397 886995725228392624930753)
                    ·
                      rfl

theorem cell22_2591127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_2591127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2591127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2591127 prefixEnd_2591127 := by exact prefixLift 2591127
  have htrace : WordTrace (prefixWord ++ tailWord_2591127) baseStart_2591127 baseEnd_2591127 := by
    simpa [prefixWord, tailWord_2591127, baseEnd_2591127] using wordTrace_append hprefix tailTrace_2591127
  have hstable : (prefixWord ++ tailWord_2591127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591127).length < 2 ^ (prefixWord ++ tailWord_2591127).sum := by decide
  have hdescent : baseEnd_2591127 < baseStart_2591127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591133 : List Nat := [1, 4, 2, 1, 4, 2, 1, 2, 1, 4]
def baseStart_2591133 : Nat := 118140960795 + 2591133 * 2 ^ 59
def prefixEnd_2591133 : Nat := 4983230072969 + 3 ^ 40 * 2591133 * 2
def baseEnd_2591133 : Nat := 886997779151010609280735

theorem tailTrace_2591133 : CollatzResearch.WordTrace tailWord_2591133 prefixEnd_2591133 886997779151010609280735 := by
  unfold tailWord_2591133
  simp only [CollatzResearch.WordTrace]
  refine ⟨94506384521775146129874053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63004256347850097419916035 94506384521775146129874053)
  ·
    refine ⟨17719947097832839899351385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94506384521775146129874053 17719947097832839899351385)
    ·
      refine ⟨13289960323374629924513539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17719947097832839899351385 13289960323374629924513539)
      ·
        refine ⟨19934940485061944886770309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13289960323374629924513539 19934940485061944886770309)
        ·
          refine ⟨3737801340949114666269433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19934940485061944886770309 3737801340949114666269433)
          ·
            refine ⟨2803351005711835999702075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3737801340949114666269433 2803351005711835999702075)
            ·
              refine ⟨4205026508567753999553113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2803351005711835999702075 4205026508567753999553113)
              ·
                refine ⟨3153769881425815499664835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4205026508567753999553113 3153769881425815499664835)
                ·
                  refine ⟨4730654822138723249497253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3153769881425815499664835 4730654822138723249497253)
                  ·
                    refine ⟨886997779151010609280735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4730654822138723249497253 886997779151010609280735)
                    ·
                      rfl

theorem cell22_2591133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_2591133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2591133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2591133 prefixEnd_2591133 := by exact prefixLift 2591133
  have htrace : WordTrace (prefixWord ++ tailWord_2591133) baseStart_2591133 baseEnd_2591133 := by
    simpa [prefixWord, tailWord_2591133, baseEnd_2591133] using wordTrace_append hprefix tailTrace_2591133
  have hstable : (prefixWord ++ tailWord_2591133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591133).length < 2 ^ (prefixWord ++ tailWord_2591133).sum := by decide
  have hdescent : baseEnd_2591133 < baseStart_2591133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591208 : List Nat := [2, 1, 4, 1, 1, 3, 1, 5, 1, 3]
def baseStart_2591208 : Nat := 118140960795 + 2591208 * 2 ^ 59
def prefixEnd_2591208 : Nat := 4983230072969 + 3 ^ 40 * 2591208 * 2
def baseEnd_2591208 : Nat := 887023453183735413655505

theorem tailTrace_2591208 : CollatzResearch.WordTrace tailWord_2591208 prefixEnd_2591208 887023453183735413655505 := by
  unfold tailWord_2591208
  simp only [CollatzResearch.WordTrace]
  refine ⟨47254559998251716969427139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63006079997668955959236185 47254559998251716969427139)
  ·
    refine ⟨70881839997377575454140709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47254559998251716969427139 70881839997377575454140709)
    ·
      refine ⟨13290344999508295397651383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70881839997377575454140709 13290344999508295397651383)
      ·
        refine ⟨19935517499262443096477075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13290344999508295397651383 19935517499262443096477075)
        ·
          refine ⟨29903276248893664644715613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19935517499262443096477075 29903276248893664644715613)
          ·
            refine ⟨11213728593335124241768355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29903276248893664644715613 11213728593335124241768355)
            ·
              refine ⟨16820592890002686362652533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11213728593335124241768355 16820592890002686362652533)
              ·
                refine ⟨1576930583437751846498675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16820592890002686362652533 1576930583437751846498675)
                ·
                  refine ⟨2365395875156627769748013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1576930583437751846498675 2365395875156627769748013)
                  ·
                    refine ⟨887023453183735413655505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2365395875156627769748013 887023453183735413655505)
                    ·
                      rfl

theorem cell22_2591208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_2591208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2591208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2591208 prefixEnd_2591208 := by exact prefixLift 2591208
  have htrace : WordTrace (prefixWord ++ tailWord_2591208) baseStart_2591208 baseEnd_2591208 := by
    simpa [prefixWord, tailWord_2591208, baseEnd_2591208] using wordTrace_append hprefix tailTrace_2591208
  have hstable : (prefixWord ++ tailWord_2591208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591208).length < 2 ^ (prefixWord ++ tailWord_2591208).sum := by decide
  have hdescent : baseEnd_2591208 < baseStart_2591208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591236 : List Nat := [2, 3, 2, 3, 1, 1, 2, 1, 2, 5]
def baseStart_2591236 : Nat := 118140960795 + 2591236 * 2 ^ 59
def prefixEnd_2591236 : Nat := 4983230072969 + 3 ^ 40 * 2591236 * 2
def baseEnd_2591236 : Nat := 887033038155952673955419

theorem tailTrace_2591236 : CollatzResearch.WordTrace tailWord_2591236 prefixEnd_2591236 887033038155952673955419 := by
  unfold tailWord_2591236
  simp only [CollatzResearch.WordTrace]
  refine ⟨47255070620200997360436781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63006760826934663147249041 47255070620200997360436781)
  ·
    refine ⟨17720651482575374010163793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47255070620200997360436781 17720651482575374010163793)
    ·
      refine ⟨13290488611931530507622845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17720651482575374010163793 13290488611931530507622845)
      ·
        refine ⟨4983933229474323940358567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13290488611931530507622845 4983933229474323940358567)
        ·
          refine ⟨7475899844211485910537851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4983933229474323940358567 7475899844211485910537851)
          ·
            refine ⟨11213849766317228865806777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7475899844211485910537851 11213849766317228865806777)
            ·
              refine ⟨8410387324737921649355083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11213849766317228865806777 8410387324737921649355083)
              ·
                refine ⟨12615580987106882474032625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8410387324737921649355083 12615580987106882474032625)
                ·
                  refine ⟨9461685740330161855524469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12615580987106882474032625 9461685740330161855524469)
                  ·
                    refine ⟨887033038155952673955419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9461685740330161855524469 887033038155952673955419)
                    ·
                      rfl

theorem cell22_2591236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_2591236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2591236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2591236 prefixEnd_2591236 := by exact prefixLift 2591236
  have htrace : WordTrace (prefixWord ++ tailWord_2591236) baseStart_2591236 baseEnd_2591236 := by
    simpa [prefixWord, tailWord_2591236, baseEnd_2591236] using wordTrace_append hprefix tailTrace_2591236
  have hstable : (prefixWord ++ tailWord_2591236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591236).length < 2 ^ (prefixWord ++ tailWord_2591236).sum := by decide
  have hdescent : baseEnd_2591236 < baseStart_2591236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591251 : List Nat := [1, 1, 1, 2, 1, 5, 4, 2, 1, 4]
def baseStart_2591251 : Nat := 118140960795 + 2591251 * 2 ^ 59
def prefixEnd_2591251 : Nat := 4983230072969 + 3 ^ 40 * 2591251 * 2
def baseEnd_2591251 : Nat := 887038172962497634830373

theorem tailTrace_2591251 : CollatzResearch.WordTrace tailWord_2591251 prefixEnd_2591251 887038172962497634830373 := by
  unfold tailWord_2591251
  simp only [CollatzResearch.WordTrace]
  refine ⟨94510688335347652282669607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63007125556898434855113071 94510688335347652282669607)
  ·
    refine ⟨141766032503021478424004411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94510688335347652282669607 141766032503021478424004411)
    ·
      refine ⟨212649048754532217636006617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141766032503021478424004411 212649048754532217636006617)
      ·
        refine ⟨159486786565899163227004963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212649048754532217636006617 159486786565899163227004963)
        ·
          refine ⟨239230179848848744840507445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159486786565899163227004963 239230179848848744840507445)
          ·
            refine ⟨22427829360829569828797573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 239230179848848744840507445 22427829360829569828797573)
            ·
              refine ⟨4205218005155544342899545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22427829360829569828797573 4205218005155544342899545)
              ·
                refine ⟨3153913503866658257174659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4205218005155544342899545 3153913503866658257174659)
                ·
                  refine ⟨4730870255799987385761989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3153913503866658257174659 4730870255799987385761989)
                  ·
                    refine ⟨887038172962497634830373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4730870255799987385761989 887038172962497634830373)
                    ·
                      rfl

theorem cell22_2591251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 2, 1, 4].length) (baseStart_2591251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2591251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2591251 prefixEnd_2591251 := by exact prefixLift 2591251
  have htrace : WordTrace (prefixWord ++ tailWord_2591251) baseStart_2591251 baseEnd_2591251 := by
    simpa [prefixWord, tailWord_2591251, baseEnd_2591251] using wordTrace_append hprefix tailTrace_2591251
  have hstable : (prefixWord ++ tailWord_2591251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591251).length < 2 ^ (prefixWord ++ tailWord_2591251).sum := by decide
  have hdescent : baseEnd_2591251 < baseStart_2591251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591281 : List Nat := [1, 2, 2, 3, 1, 1, 4, 1, 4, 3]
def baseStart_2591281 : Nat := 118140960795 + 2591281 * 2 ^ 59
def prefixEnd_2591281 : Nat := 4983230072969 + 3 ^ 40 * 2591281 * 2
def baseEnd_2591281 : Nat := 887048442575587556580281

theorem tailTrace_2591281 : CollatzResearch.WordTrace tailWord_2591281 prefixEnd_2591281 887048442575587556580281 := by
  unfold tailWord_2591281
  simp only [CollatzResearch.WordTrace]
  refine ⟨94511782525238967406261697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63007855016825978270841131 94511782525238967406261697)
  ·
    refine ⟨70883836893929225554696273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94511782525238967406261697 70883836893929225554696273)
    ·
      refine ⟨53162877670446919166022205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70883836893929225554696273 53162877670446919166022205)
      ·
        refine ⟨19936079126417594687258327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53162877670446919166022205 19936079126417594687258327)
        ·
          refine ⟨29904118689626392030887491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19936079126417594687258327 29904118689626392030887491)
          ·
            refine ⟨44856178034439588046331237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29904118689626392030887491 44856178034439588046331237)
            ·
              refine ⟨8410533381457422758687107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44856178034439588046331237 8410533381457422758687107)
              ·
                refine ⟨12615800072186134138030661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8410533381457422758687107 12615800072186134138030661)
                ·
                  refine ⟨2365462513534900150880749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12615800072186134138030661 2365462513534900150880749)
                  ·
                    refine ⟨887048442575587556580281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2365462513534900150880749 887048442575587556580281)
                    ·
                      rfl

theorem cell22_2591281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 4, 3].length) (baseStart_2591281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2591281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2591281 prefixEnd_2591281 := by exact prefixLift 2591281
  have htrace : WordTrace (prefixWord ++ tailWord_2591281) baseStart_2591281 baseEnd_2591281 := by
    simpa [prefixWord, tailWord_2591281, baseEnd_2591281] using wordTrace_append hprefix tailTrace_2591281
  have hstable : (prefixWord ++ tailWord_2591281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591281).length < 2 ^ (prefixWord ++ tailWord_2591281).sum := by decide
  have hdescent : baseEnd_2591281 < baseStart_2591281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591283 : List Nat := [1, 1, 1, 2, 4, 2, 5, 2, 4]
def baseStart_2591283 : Nat := 118140960795 + 2591283 * 2 ^ 59
def prefixEnd_2591283 : Nat := 4983230072969 + 3 ^ 40 * 2591283 * 2
def baseEnd_2591283 : Nat := 295683042405486739343425

theorem tailTrace_2591283 : CollatzResearch.WordTrace tailWord_2591283 prefixEnd_2591283 295683042405486739343425 := by
  unfold tailWord_2591283
  simp only [CollatzResearch.WordTrace]
  refine ⟨94511855471231721747834503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63007903647487814498556335 94511855471231721747834503)
  ·
    refine ⟨141767783206847582621751755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94511855471231721747834503 141767783206847582621751755)
    ·
      refine ⟨212651674810271373932627633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141767783206847582621751755 212651674810271373932627633)
      ·
        refine ⟨159488756107703530449470725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212651674810271373932627633 159488756107703530449470725)
        ·
          refine ⟨29904141770194411959275761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 159488756107703530449470725 29904141770194411959275761)
          ·
            refine ⟨22428106327645808969456821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29904141770194411959275761 22428106327645808969456821)
            ·
              refine ⟨2102634968216794590886577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22428106327645808969456821 2102634968216794590886577)
              ·
                refine ⟨1576976226162595943164933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2102634968216794590886577 1576976226162595943164933)
                ·
                  refine ⟨295683042405486739343425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1576976226162595943164933 295683042405486739343425)
                  ·
                    rfl

theorem cell22_2591283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 2, 4].length) (baseStart_2591283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2591283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2591283 prefixEnd_2591283 := by exact prefixLift 2591283
  have htrace : WordTrace (prefixWord ++ tailWord_2591283) baseStart_2591283 baseEnd_2591283 := by
    simpa [prefixWord, tailWord_2591283, baseEnd_2591283] using wordTrace_append hprefix tailTrace_2591283
  have hstable : (prefixWord ++ tailWord_2591283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591283).length < 2 ^ (prefixWord ++ tailWord_2591283).sum := by decide
  have hdescent : baseEnd_2591283 < baseStart_2591283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591302 : List Nat := [6, 1, 1, 1, 2, 3, 1, 2, 1, 4]
def baseStart_2591302 : Nat := 118140960795 + 2591302 * 2 ^ 59
def prefixEnd_2591302 : Nat := 4983230072969 + 3 ^ 40 * 2591302 * 2
def baseEnd_2591302 : Nat := 887055631304750501805217

theorem tailTrace_2591302 : CollatzResearch.WordTrace tailWord_2591302 prefixEnd_2591302 887055631304750501805217 := by
  unfold tailWord_2591302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2953517139317590249774255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 63008365638775258661850773 2953517139317590249774255)
  ·
    refine ⟨4430275708976385374661383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2953517139317590249774255 4430275708976385374661383)
    ·
      refine ⟨6645413563464578061992075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4430275708976385374661383 6645413563464578061992075)
      ·
        refine ⟨9968120345196867092988113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6645413563464578061992075 9968120345196867092988113)
        ·
          refine ⟨7476090258897650319741085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9968120345196867092988113 7476090258897650319741085)
          ·
            refine ⟨2803533847086618869902907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7476090258897650319741085 2803533847086618869902907)
            ·
              refine ⟨4205300770629928304854361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2803533847086618869902907 4205300770629928304854361)
              ·
                refine ⟨3153975577972446228640771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4205300770629928304854361 3153975577972446228640771)
                ·
                  refine ⟨4730963366958669342961157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3153975577972446228640771 4730963366958669342961157)
                  ·
                    refine ⟨887055631304750501805217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4730963366958669342961157 887055631304750501805217)
                    ·
                      rfl

theorem cell22_2591302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_2591302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2591302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2591302 prefixEnd_2591302 := by exact prefixLift 2591302
  have htrace : WordTrace (prefixWord ++ tailWord_2591302) baseStart_2591302 baseEnd_2591302 := by
    simpa [prefixWord, tailWord_2591302, baseEnd_2591302] using wordTrace_append hprefix tailTrace_2591302
  have hstable : (prefixWord ++ tailWord_2591302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591302).length < 2 ^ (prefixWord ++ tailWord_2591302).sum := by decide
  have hdescent : baseEnd_2591302 < baseStart_2591302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591341 : List Nat := [1, 5, 1, 1, 3, 1, 1, 1, 2, 6]
def baseStart_2591341 : Nat := 118140960795 + 2591341 * 2 ^ 59
def prefixEnd_2591341 : Nat := 4983230072969 + 3 ^ 40 * 2591341 * 2
def baseEnd_2591341 : Nat := 887068981801767400080097

theorem tailTrace_2591341 : CollatzResearch.WordTrace tailWord_2591341 prefixEnd_2591341 887068981801767400080097 := by
  unfold tailWord_2591341
  simp only [CollatzResearch.WordTrace]
  refine ⟨94513970905021597653445877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63009313936681065102297251 94513970905021597653445877)
  ·
    refine ⟨8860684772345774780010551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94513970905021597653445877 8860684772345774780010551)
    ·
      refine ⟨13291027158518662170015827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8860684772345774780010551 13291027158518662170015827)
      ·
        refine ⟨19936540737777993255023741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13291027158518662170015827 19936540737777993255023741)
        ·
          refine ⟨7476202776666747470633903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19936540737777993255023741 7476202776666747470633903)
          ·
            refine ⟨11214304165000121205950855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7476202776666747470633903 11214304165000121205950855)
            ·
              refine ⟨16821456247500181808926283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11214304165000121205950855 16821456247500181808926283)
              ·
                refine ⟨25232184371250272713389425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16821456247500181808926283 25232184371250272713389425)
                ·
                  refine ⟨18924138278437704535042069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25232184371250272713389425 18924138278437704535042069)
                  ·
                    refine ⟨887068981801767400080097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18924138278437704535042069 887068981801767400080097)
                    ·
                      rfl

theorem cell22_2591341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_2591341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2591341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2591341 prefixEnd_2591341 := by exact prefixLift 2591341
  have htrace : WordTrace (prefixWord ++ tailWord_2591341) baseStart_2591341 baseEnd_2591341 := by
    simpa [prefixWord, tailWord_2591341, baseEnd_2591341] using wordTrace_append hprefix tailTrace_2591341
  have hstable : (prefixWord ++ tailWord_2591341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591341).length < 2 ^ (prefixWord ++ tailWord_2591341).sum := by decide
  have hdescent : baseEnd_2591341 < baseStart_2591341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591356 : List Nat := [2, 2, 2, 1, 1, 2, 4, 3, 5]
def baseStart_2591356 : Nat := 118140960795 + 2591356 * 2 ^ 59
def prefixEnd_2591356 : Nat := 4983230072969 + 3 ^ 40 * 2591356 * 2
def baseEnd_2591356 : Nat := 295691372202770786985017

theorem tailTrace_2591356 : CollatzResearch.WordTrace tailWord_2591356 prefixEnd_2591356 295691372202770786985017 := by
  unfold tailWord_2591356
  simp only [CollatzResearch.WordTrace]
  refine ⟨47257258999983627607620961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63009678666644836810161281 47257258999983627607620961)
  ·
    refine ⟨35442944249987720705715721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47257258999983627607620961 35442944249987720705715721)
    ·
      refine ⟨26582208187490790529286791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35442944249987720705715721 26582208187490790529286791)
      ·
        refine ⟨39873312281236185793930187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26582208187490790529286791 39873312281236185793930187)
        ·
          refine ⟨59809968421854278690895281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39873312281236185793930187 59809968421854278690895281)
          ·
            refine ⟨44857476316390709018171461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59809968421854278690895281 44857476316390709018171461)
            ·
              refine ⟨8410776809323257940907149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44857476316390709018171461 8410776809323257940907149)
              ·
                refine ⟨3154041303496221727840181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8410776809323257940907149 3154041303496221727840181)
                ·
                  refine ⟨295691372202770786985017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3154041303496221727840181 295691372202770786985017)
                  ·
                    rfl

theorem cell22_2591356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 3, 5].length) (baseStart_2591356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2591356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2591356 prefixEnd_2591356 := by exact prefixLift 2591356
  have htrace : WordTrace (prefixWord ++ tailWord_2591356) baseStart_2591356 baseEnd_2591356 := by
    simpa [prefixWord, tailWord_2591356, baseEnd_2591356] using wordTrace_append hprefix tailTrace_2591356
  have hstable : (prefixWord ++ tailWord_2591356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591356).length < 2 ^ (prefixWord ++ tailWord_2591356).sum := by decide
  have hdescent : baseEnd_2591356 < baseStart_2591356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591448 : List Nat := [2, 1, 2, 2, 3, 3, 1, 2, 2, 4]
def baseStart_2591448 : Nat := 118140960795 + 2591448 * 2 ^ 59
def prefixEnd_2591448 : Nat := 4983230072969 + 3 ^ 40 * 2591448 * 2
def baseEnd_2591448 : Nat := 887105610088454787654769

theorem tailTrace_2591448 : CollatzResearch.WordTrace tailWord_2591448 prefixEnd_2591448 887105610088454787654769 := by
  unfold tailWord_2591448
  simp only [CollatzResearch.WordTrace]
  refine ⟨47258936757816977463795499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63011915677089303285060665 47258936757816977463795499)
  ·
    refine ⟨70888405136725466195693249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47258936757816977463795499 70888405136725466195693249)
    ·
      refine ⟨53166303852544099646769937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70888405136725466195693249 53166303852544099646769937)
      ·
        refine ⟨39874727889408074735077453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53166303852544099646769937 39874727889408074735077453)
        ·
          refine ⟨14953022958528028025654045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39874727889408074735077453 14953022958528028025654045)
          ·
            refine ⟨5607383609448010509620267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14953022958528028025654045 5607383609448010509620267)
            ·
              refine ⟨8411075414172015764430401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5607383609448010509620267 8411075414172015764430401)
              ·
                refine ⟨6308306560629011823322801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8411075414172015764430401 6308306560629011823322801)
                ·
                  refine ⟨4731229920471758867492101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6308306560629011823322801 4731229920471758867492101)
                  ·
                    refine ⟨887105610088454787654769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4731229920471758867492101 887105610088454787654769)
                    ·
                      rfl

theorem cell22_2591448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 2, 4].length) (baseStart_2591448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2591448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2591448 prefixEnd_2591448 := by exact prefixLift 2591448
  have htrace : WordTrace (prefixWord ++ tailWord_2591448) baseStart_2591448 baseEnd_2591448 := by
    simpa [prefixWord, tailWord_2591448, baseEnd_2591448] using wordTrace_append hprefix tailTrace_2591448
  have hstable : (prefixWord ++ tailWord_2591448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591448).length < 2 ^ (prefixWord ++ tailWord_2591448).sum := by decide
  have hdescent : baseEnd_2591448 < baseStart_2591448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591538 : List Nat := [3, 2, 1, 1, 3, 1, 1, 3, 3, 4]
def baseStart_2591538 : Nat := 118140960795 + 2591538 * 2 ^ 59
def prefixEnd_2591538 : Nat := 4983230072969 + 3 ^ 40 * 2591538 * 2
def baseEnd_2591538 : Nat := 887136418927724552904493

theorem tailTrace_2591538 : CollatzResearch.WordTrace tailWord_2591538 prefixEnd_2591538 887136418927724552904493 := by
  unfold tailWord_2591538
  simp only [CollatzResearch.WordTrace]
  refine ⟨23630289021326975074591817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63014104056871933532244845 23630289021326975074591817)
  ·
    refine ⟨17722716765995231305943863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23630289021326975074591817 17722716765995231305943863)
    ·
      refine ⟨26584075148992846958915795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17722716765995231305943863 26584075148992846958915795)
      ·
        refine ⟨39876112723489270438373693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26584075148992846958915795 39876112723489270438373693)
        ·
          refine ⟨14953542271308476414390135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39876112723489270438373693 14953542271308476414390135)
          ·
            refine ⟨22430313406962714621585203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14953542271308476414390135 22430313406962714621585203)
            ·
              refine ⟨33645470110444071932377805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22430313406962714621585203 33645470110444071932377805)
              ·
                refine ⟨12617051291416526974641677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33645470110444071932377805 12617051291416526974641677)
                ·
                  refine ⟨4731394234281197615490629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12617051291416526974641677 4731394234281197615490629)
                  ·
                    refine ⟨887136418927724552904493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4731394234281197615490629 887136418927724552904493)
                    ·
                      rfl

theorem cell22_2591538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_2591538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2591538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2591538 prefixEnd_2591538 := by exact prefixLift 2591538
  have htrace : WordTrace (prefixWord ++ tailWord_2591538) baseStart_2591538 baseEnd_2591538 := by
    simpa [prefixWord, tailWord_2591538, baseEnd_2591538] using wordTrace_append hprefix tailTrace_2591538
  have hstable : (prefixWord ++ tailWord_2591538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591538).length < 2 ^ (prefixWord ++ tailWord_2591538).sum := by decide
  have hdescent : baseEnd_2591538 < baseStart_2591538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591570 : List Nat := [3, 2, 2, 1, 1, 2, 1, 6, 4]
def baseStart_2591570 : Nat := 118140960795 + 2591570 * 2 ^ 59
def prefixEnd_2591570 : Nat := 4983230072969 + 3 ^ 40 * 2591570 * 2
def baseEnd_2591570 : Nat := 295715791060562378701465

theorem tailTrace_2591570 : CollatzResearch.WordTrace tailWord_2591570 prefixEnd_2591570 295715791060562378701465 := by
  unfold tailWord_2591570
  simp only [CollatzResearch.WordTrace]
  refine ⟨23630580805297992440883041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63014882147461313175688109 23630580805297992440883041)
  ·
    refine ⟨17722935603973494330662281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23630580805297992440883041 17722935603973494330662281)
    ·
      refine ⟨13292201702980120747996711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17722935603973494330662281 13292201702980120747996711)
      ·
        refine ⟨19938302554470181121995067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13292201702980120747996711 19938302554470181121995067)
        ·
          refine ⟨29907453831705271682992601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19938302554470181121995067 29907453831705271682992601)
          ·
            refine ⟨22430590373778953762244451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29907453831705271682992601 22430590373778953762244451)
            ·
              refine ⟨33645885560668430643366677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22430590373778953762244451 33645885560668430643366677)
              ·
                refine ⟨1577150885656332686407813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33645885560668430643366677 1577150885656332686407813)
                ·
                  refine ⟨295715791060562378701465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1577150885656332686407813 295715791060562378701465)
                  ·
                    rfl

theorem cell22_2591570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 6, 4].length) (baseStart_2591570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2591570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2591570 prefixEnd_2591570 := by exact prefixLift 2591570
  have htrace : WordTrace (prefixWord ++ tailWord_2591570) baseStart_2591570 baseEnd_2591570 := by
    simpa [prefixWord, tailWord_2591570, baseEnd_2591570] using wordTrace_append hprefix tailTrace_2591570
  have hstable : (prefixWord ++ tailWord_2591570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591570).length < 2 ^ (prefixWord ++ tailWord_2591570).sum := by decide
  have hdescent : baseEnd_2591570 < baseStart_2591570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591677 : List Nat := [1, 4, 1, 2, 4, 1, 2, 2, 5]
def baseStart_2591677 : Nat := 118140960795 + 2591677 * 2 ^ 59
def prefixEnd_2591677 : Nat := 4983230072969 + 3 ^ 40 * 2591677 * 2
def baseEnd_2591677 : Nat := 295728000489458174559689

theorem tailTrace_2591677 : CollatzResearch.WordTrace tailWord_2591677 prefixEnd_2591677 295728000489458174559689 := by
  unfold tailWord_2591677
  simp only [CollatzResearch.WordTrace]
  refine ⟨94526225831804327037677285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63017483887869551358451523 94526225831804327037677285)
  ·
    refine ⟨17723667343463311319564491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94526225831804327037677285 17723667343463311319564491)
    ·
      refine ⟨26585501015194966979346737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17723667343463311319564491 26585501015194966979346737)
      ·
        refine ⟨19939125761396225234510053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26585501015194966979346737 19939125761396225234510053)
        ·
          refine ⟨3738586080261792231470635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19939125761396225234510053 3738586080261792231470635)
          ·
            refine ⟨5607879120392688347205953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3738586080261792231470635 5607879120392688347205953)
            ·
              refine ⟨4205909340294516260404465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5607879120392688347205953 4205909340294516260404465)
              ·
                refine ⟨3154432005220887195303349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4205909340294516260404465 3154432005220887195303349)
                ·
                  refine ⟨295728000489458174559689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3154432005220887195303349 295728000489458174559689)
                  ·
                    rfl

theorem cell22_2591677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_2591677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2591677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2591677 prefixEnd_2591677 := by exact prefixLift 2591677
  have htrace : WordTrace (prefixWord ++ tailWord_2591677) baseStart_2591677 baseEnd_2591677 := by
    simpa [prefixWord, tailWord_2591677, baseEnd_2591677] using wordTrace_append hprefix tailTrace_2591677
  have hstable : (prefixWord ++ tailWord_2591677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591677).length < 2 ^ (prefixWord ++ tailWord_2591677).sum := by decide
  have hdescent : baseEnd_2591677 < baseStart_2591677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591705 : List Nat := [1, 2, 1, 2, 5, 2, 1, 2, 6]
def baseStart_2591705 : Nat := 118140960795 + 2591705 * 2 ^ 59
def prefixEnd_2591705 : Nat := 4983230072969 + 3 ^ 40 * 2591705 * 2
def baseEnd_2591705 : Nat := 295731195480197261326327

theorem tailTrace_2591705 : CollatzResearch.WordTrace tailWord_2591705 prefixEnd_2591705 295731195480197261326327 := by
  unfold tailWord_2591705
  simp only [CollatzResearch.WordTrace]
  refine ⟨94527247075702887819696569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63018164717135258546464379 94527247075702887819696569)
  ·
    refine ⟨70895435306777165864772427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94527247075702887819696569 70895435306777165864772427)
    ·
      refine ⟨106343152960165748797158641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70895435306777165864772427 106343152960165748797158641)
      ·
        refine ⟨79757364720124311597868981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106343152960165748797158641 79757364720124311597868981)
        ·
          refine ⟨7477252942511654212300217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79757364720124311597868981 7477252942511654212300217)
          ·
            refine ⟨5607939706883740659225163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7477252942511654212300217 5607939706883740659225163)
            ·
              refine ⟨8411909560325610988837745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5607939706883740659225163 8411909560325610988837745)
              ·
                refine ⟨6308932170244208241628309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8411909560325610988837745 6308932170244208241628309)
                ·
                  refine ⟨295731195480197261326327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6308932170244208241628309 295731195480197261326327)
                  ·
                    rfl

theorem cell22_2591705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 6].length) (baseStart_2591705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2591705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2591705 prefixEnd_2591705 := by exact prefixLift 2591705
  have htrace : WordTrace (prefixWord ++ tailWord_2591705) baseStart_2591705 baseEnd_2591705 := by
    simpa [prefixWord, tailWord_2591705, baseEnd_2591705] using wordTrace_append hprefix tailTrace_2591705
  have hstable : (prefixWord ++ tailWord_2591705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591705).length < 2 ^ (prefixWord ++ tailWord_2591705).sum := by decide
  have hdescent : baseEnd_2591705 < baseStart_2591705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591720 : List Nat := [2, 1, 4, 1, 1, 1, 4, 2, 1, 5]
def baseStart_2591720 : Nat := 118140960795 + 2591720 * 2 ^ 59
def prefixEnd_2591720 : Nat := 4983230072969 + 3 ^ 40 * 2591720 * 2
def baseEnd_2591720 : Nat := 887198721247136744853935

theorem tailTrace_2591720 : CollatzResearch.WordTrace tailWord_2591720 prefixEnd_2591720 887198721247136744853935 := by
  unfold tailWord_2591720
  simp only [CollatzResearch.WordTrace]
  refine ⟨47263897085324272690746307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63018529447099030254328409 47263897085324272690746307)
  ·
    refine ⟨70895845627986409036119461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47263897085324272690746307 70895845627986409036119461)
    ·
      refine ⟨13292971055247451694272399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70895845627986409036119461 13292971055247451694272399)
      ·
        refine ⟨19939456582871177541408599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13292971055247451694272399 19939456582871177541408599)
        ·
          refine ⟨29909184874306766312112899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19939456582871177541408599 29909184874306766312112899)
          ·
            refine ⟨44863777311460149468169349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29909184874306766312112899 44863777311460149468169349)
            ·
              refine ⟨8411958245898778025281753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44863777311460149468169349 8411958245898778025281753)
              ·
                refine ⟨6308968684424083518961315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8411958245898778025281753 6308968684424083518961315)
                ·
                  refine ⟨9463453026636125278441973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6308968684424083518961315 9463453026636125278441973)
                  ·
                    refine ⟨887198721247136744853935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9463453026636125278441973 887198721247136744853935)
                    ·
                      rfl

theorem cell22_2591720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_2591720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2591720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2591720 prefixEnd_2591720 := by exact prefixLift 2591720
  have htrace : WordTrace (prefixWord ++ tailWord_2591720) baseStart_2591720 baseEnd_2591720 := by
    simpa [prefixWord, tailWord_2591720, baseEnd_2591720] using wordTrace_append hprefix tailTrace_2591720
  have hstable : (prefixWord ++ tailWord_2591720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591720).length < 2 ^ (prefixWord ++ tailWord_2591720).sum := by decide
  have hdescent : baseEnd_2591720 < baseStart_2591720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591722 : List Nat := [3, 1, 3, 1, 2, 2, 1, 5, 4]
def baseStart_2591722 : Nat := 118140960795 + 2591722 * 2 ^ 59
def prefixEnd_2591722 : Nat := 4983230072969 + 3 ^ 40 * 2591722 * 2
def baseEnd_2591722 : Nat := 295733135296003135434643

theorem tailTrace_2591722 : CollatzResearch.WordTrace tailWord_2591722 prefixEnd_2591722 295733135296003135434643 := by
  unfold tailWord_2591722
  simp only [CollatzResearch.WordTrace]
  refine ⟨23631966779160324930766355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63018578077760866482043613 23631966779160324930766355)
  ·
    refine ⟨35447950168740487396149533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23631966779160324930766355 35447950168740487396149533)
    ·
      refine ⟨13292981313277682773556075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35447950168740487396149533 13292981313277682773556075)
      ·
        refine ⟨19939471969916524160334113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13292981313277682773556075 19939471969916524160334113)
        ·
          refine ⟨14954603977437393120250585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19939471969916524160334113 14954603977437393120250585)
          ·
            refine ⟨11215952983078044840187939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14954603977437393120250585 11215952983078044840187939)
            ·
              refine ⟨16823929474617067260281909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11215952983078044840187939 16823929474617067260281909)
              ·
                refine ⟨1577243388245350055651429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16823929474617067260281909 1577243388245350055651429)
                ·
                  refine ⟨295733135296003135434643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1577243388245350055651429 295733135296003135434643)
                  ·
                    rfl

theorem cell22_2591722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 5, 4].length) (baseStart_2591722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2591722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2591722 prefixEnd_2591722 := by exact prefixLift 2591722
  have htrace : WordTrace (prefixWord ++ tailWord_2591722) baseStart_2591722 baseEnd_2591722 := by
    simpa [prefixWord, tailWord_2591722, baseEnd_2591722] using wordTrace_append hprefix tailTrace_2591722
  have hstable : (prefixWord ++ tailWord_2591722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591722).length < 2 ^ (prefixWord ++ tailWord_2591722).sum := by decide
  have hdescent : baseEnd_2591722 < baseStart_2591722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591767 : List Nat := [1, 1, 3, 5, 1, 1, 4, 6]
def baseStart_2591767 : Nat := 118140960795 + 2591767 * 2 ^ 59
def prefixEnd_2591767 : Nat := 4983230072969 + 3 ^ 40 * 2591767 * 2
def baseEnd_2591767 : Nat := 98579423367516032103199

theorem tailTrace_2591767 : CollatzResearch.WordTrace tailWord_2591767 prefixEnd_2591767 98579423367516032103199 := by
  unfold tailWord_2591767
  simp only [CollatzResearch.WordTrace]
  refine ⟨94529508401478272408453555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63019672267652181605635703 94529508401478272408453555)
  ·
    refine ⟨141794262602217408612680333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94529508401478272408453555 141794262602217408612680333)
    ·
      refine ⟨53172848475831528229755125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141794262602217408612680333 53172848475831528229755125)
      ·
        refine ⟨4984954544609205771539543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53172848475831528229755125 4984954544609205771539543)
        ·
          refine ⟨7477431816913808657309315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4984954544609205771539543 7477431816913808657309315)
          ·
            refine ⟨11216147725370712985963973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7477431816913808657309315 11216147725370712985963973)
            ·
              refine ⟨2103027698507008684868245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11216147725370712985963973 2103027698507008684868245)
              ·
                refine ⟨98579423367516032103199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2103027698507008684868245 98579423367516032103199)
                ·
                  rfl

theorem cell22_2591767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 6].length) (baseStart_2591767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2591767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2591767 prefixEnd_2591767 := by exact prefixLift 2591767
  have htrace : WordTrace (prefixWord ++ tailWord_2591767) baseStart_2591767 baseEnd_2591767 := by
    simpa [prefixWord, tailWord_2591767, baseEnd_2591767] using wordTrace_append hprefix tailTrace_2591767
  have hstable : (prefixWord ++ tailWord_2591767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591767).length < 2 ^ (prefixWord ++ tailWord_2591767).sum := by decide
  have hdescent : baseEnd_2591767 < baseStart_2591767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591795 : List Nat := [1, 1, 1, 2, 4, 1, 1, 6, 5]
def baseStart_2591795 : Nat := 118140960795 + 2591795 * 2 ^ 59
def prefixEnd_2591795 : Nat := 4983230072969 + 3 ^ 40 * 2591795 * 2
def baseEnd_2591795 : Nat := 295741465093287183076235

theorem tailTrace_2591795 : CollatzResearch.WordTrace tailWord_2591795 prefixEnd_2591795 295741465093287183076235 := by
  unfold tailWord_2591795
  simp only [CollatzResearch.WordTrace]
  refine ⟨94530529645376833190472839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63020353096917888793648559 94530529645376833190472839)
  ·
    refine ⟨141795794468065249785709259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94530529645376833190472839 141795794468065249785709259)
    ·
      refine ⟨212693691702097874678563889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141795794468065249785709259 212693691702097874678563889)
      ·
        refine ⟨159520268776573406008922917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212693691702097874678563889 159520268776573406008922917)
        ·
          refine ⟨29910050395607513626673047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 159520268776573406008922917 29910050395607513626673047)
          ·
            refine ⟨44865075593411270440009571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29910050395607513626673047 44865075593411270440009571)
            ·
              refine ⟨67297613390116905660014357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44865075593411270440009571 67297613390116905660014357)
              ·
                refine ⟨3154575627661729952813173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67297613390116905660014357 3154575627661729952813173)
                ·
                  refine ⟨295741465093287183076235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3154575627661729952813173 295741465093287183076235)
                  ·
                    rfl

theorem cell22_2591795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 6, 5].length) (baseStart_2591795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2591795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2591795 prefixEnd_2591795 := by exact prefixLift 2591795
  have htrace : WordTrace (prefixWord ++ tailWord_2591795) baseStart_2591795 baseEnd_2591795 := by
    simpa [prefixWord, tailWord_2591795, baseEnd_2591795] using wordTrace_append hprefix tailTrace_2591795
  have hstable : (prefixWord ++ tailWord_2591795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591795).length < 2 ^ (prefixWord ++ tailWord_2591795).sum := by decide
  have hdescent : baseEnd_2591795 < baseStart_2591795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591855 : List Nat := [1, 1, 2, 1, 3, 3, 1, 2, 3, 5]
def baseStart_2591855 : Nat := 118140960795 + 2591855 * 2 ^ 59
def prefixEnd_2591855 : Nat := 4983230072969 + 3 ^ 40 * 2591855 * 2
def baseEnd_2591855 : Nat := 887244934506041392728521

theorem tailTrace_2591855 : CollatzResearch.WordTrace tailWord_2591855 prefixEnd_2591855 887244934506041392728521 := by
  unfold tailWord_2591855
  simp only [CollatzResearch.WordTrace]
  refine ⟨94532718025159463437657019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63021812016772975625104679 94532718025159463437657019)
  ·
    refine ⟨141799077037739195156485529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94532718025159463437657019 141799077037739195156485529)
    ·
      refine ⟨106349307778304396367364147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141799077037739195156485529 106349307778304396367364147)
      ·
        refine ⟨159523961667456594551046221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106349307778304396367364147 159523961667456594551046221)
        ·
          refine ⟨59821485625296222956642333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159523961667456594551046221 59821485625296222956642333)
          ·
            refine ⟨22433057109486083608740875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59821485625296222956642333 22433057109486083608740875)
            ·
              refine ⟨33649585664229125413111313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22433057109486083608740875 33649585664229125413111313)
              ·
                refine ⟨25237189248171844059833485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33649585664229125413111313 25237189248171844059833485)
                ·
                  refine ⟨9463945968064441522437557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25237189248171844059833485 9463945968064441522437557)
                  ·
                    refine ⟨887244934506041392728521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9463945968064441522437557 887244934506041392728521)
                    ·
                      rfl

theorem cell22_2591855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 5].length) (baseStart_2591855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2591855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2591855 prefixEnd_2591855 := by exact prefixLift 2591855
  have htrace : WordTrace (prefixWord ++ tailWord_2591855) baseStart_2591855 baseEnd_2591855 := by
    simpa [prefixWord, tailWord_2591855, baseEnd_2591855] using wordTrace_append hprefix tailTrace_2591855
  have hstable : (prefixWord ++ tailWord_2591855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591855).length < 2 ^ (prefixWord ++ tailWord_2591855).sum := by decide
  have hdescent : baseEnd_2591855 < baseStart_2591855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591906 : List Nat := [3, 3, 1, 3, 2, 1, 1, 1, 4, 3]
def baseStart_2591906 : Nat := 118140960795 + 2591906 * 2 ^ 59
def prefixEnd_2591906 : Nat := 4983230072969 + 3 ^ 40 * 2591906 * 2
def baseEnd_2591906 : Nat := 887262392848294259703365

theorem tailTrace_2591906 : CollatzResearch.WordTrace tailWord_2591906 prefixEnd_2591906 887262392848294259703365 := by
  unfold tailWord_2591906
  simp only [CollatzResearch.WordTrace]
  refine ⟨23633644536993674786940893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63023052098649799431842381 23633644536993674786940893)
  ·
    refine ⟨8862616701372628045102835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23633644536993674786940893 8862616701372628045102835)
    ·
      refine ⟨13293925052058942067654253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8862616701372628045102835 13293925052058942067654253)
      ·
        refine ⟨4985221894522103275370345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13293925052058942067654253 4985221894522103275370345)
        ·
          refine ⟨3738916420891577456527759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4985221894522103275370345 3738916420891577456527759)
          ·
            refine ⟨5608374631337366184791639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3738916420891577456527759 5608374631337366184791639)
            ·
              refine ⟨8412561947006049277187459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5608374631337366184791639 8412561947006049277187459)
              ·
                refine ⟨12618842920509073915781189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8412561947006049277187459 12618842920509073915781189)
                ·
                  refine ⟨2366033047595451359208973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12618842920509073915781189 2366033047595451359208973)
                  ·
                    refine ⟨887262392848294259703365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2366033047595451359208973 887262392848294259703365)
                    ·
                      rfl

theorem cell22_2591906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_2591906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2591906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2591906 prefixEnd_2591906 := by exact prefixLift 2591906
  have htrace : WordTrace (prefixWord ++ tailWord_2591906) baseStart_2591906 baseEnd_2591906 := by
    simpa [prefixWord, tailWord_2591906, baseEnd_2591906] using wordTrace_append hprefix tailTrace_2591906
  have hstable : (prefixWord ++ tailWord_2591906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591906).length < 2 ^ (prefixWord ++ tailWord_2591906).sum := by decide
  have hdescent : baseEnd_2591906 < baseStart_2591906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591936 : List Nat := [2, 1, 1, 2, 7, 1, 2, 6]
def baseStart_2591936 : Nat := 118140960795 + 2591936 * 2 ^ 59
def prefixEnd_2591936 : Nat := 4983230072969 + 3 ^ 40 * 2591936 * 2
def baseEnd_2591936 : Nat := 98585851384598242383697

theorem tailTrace_2591936 : CollatzResearch.WordTrace tailWord_2591936 prefixEnd_2591936 98585851384598242383697 := by
  unfold tailWord_2591936
  simp only [CollatzResearch.WordTrace]
  refine ⟨47267836168933007135677831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63023781558577342847570441 47267836168933007135677831)
  ·
    refine ⟨70901754253399510703516747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47267836168933007135677831 70901754253399510703516747)
    ·
      refine ⟨106352631380099266055275121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70901754253399510703516747 106352631380099266055275121)
      ·
        refine ⟨79764473535074449541456341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106352631380099266055275121 79764473535074449541456341)
        ·
          refine ⟨1869479848478307411127883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 79764473535074449541456341 1869479848478307411127883)
          ·
            refine ⟨2804219772717461116691825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1869479848478307411127883 2804219772717461116691825)
            ·
              refine ⟨2103164829538095837518869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2804219772717461116691825 2103164829538095837518869)
              ·
                refine ⟨98585851384598242383697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2103164829538095837518869 98585851384598242383697)
                ·
                  rfl

theorem cell22_2591936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 6].length) (baseStart_2591936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2591936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2591936 prefixEnd_2591936 := by exact prefixLift 2591936
  have htrace : WordTrace (prefixWord ++ tailWord_2591936) baseStart_2591936 baseEnd_2591936 := by
    simpa [prefixWord, tailWord_2591936, baseEnd_2591936] using wordTrace_append hprefix tailTrace_2591936
  have hstable : (prefixWord ++ tailWord_2591936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591936).length < 2 ^ (prefixWord ++ tailWord_2591936).sum := by decide
  have hdescent : baseEnd_2591936 < baseStart_2591936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591942 : List Nat := [6, 1, 2, 2, 1, 2, 1, 3, 4]
def baseStart_2591942 : Nat := 118140960795 + 2591942 * 2 ^ 59
def prefixEnd_2591942 : Nat := 4983230072969 + 3 ^ 40 * 2591942 * 2
def baseEnd_2591942 : Nat := 295758238794667388601085

theorem tailTrace_2591942 : CollatzResearch.WordTrace tailWord_2591942 prefixEnd_2591942 295758238794667388601085 := by
  unfold tailWord_2591942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2954246599245133665502315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 63023927450562851530716053 2954246599245133665502315)
  ·
    refine ⟨4431369898867700498253473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2954246599245133665502315 4431369898867700498253473)
    ·
      refine ⟨3323527424150775373690105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4431369898867700498253473 3323527424150775373690105)
      ·
        refine ⟨2492645568113081530267579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3323527424150775373690105 2492645568113081530267579)
        ·
          refine ⟨3738968352169622295401369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2492645568113081530267579 3738968352169622295401369)
          ·
            refine ⟨2804226264127216721551027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3738968352169622295401369 2804226264127216721551027)
            ·
              refine ⟨4206339396190825082326541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2804226264127216721551027 4206339396190825082326541)
              ·
                refine ⟨1577377273571559405872453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4206339396190825082326541 1577377273571559405872453)
                ·
                  refine ⟨295758238794667388601085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1577377273571559405872453 295758238794667388601085)
                  ·
                    rfl

theorem cell22_2591942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_2591942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2591942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2591942 prefixEnd_2591942 := by exact prefixLift 2591942
  have htrace : WordTrace (prefixWord ++ tailWord_2591942) baseStart_2591942 baseEnd_2591942 := by
    simpa [prefixWord, tailWord_2591942, baseEnd_2591942] using wordTrace_append hprefix tailTrace_2591942
  have hstable : (prefixWord ++ tailWord_2591942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591942).length < 2 ^ (prefixWord ++ tailWord_2591942).sum := by decide
  have hdescent : baseEnd_2591942 < baseStart_2591942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591968 : List Nat := [2, 1, 1, 3, 1, 5, 3, 2, 1, 3]
def baseStart_2591968 : Nat := 118140960795 + 2591968 * 2 ^ 59
def prefixEnd_2591968 : Nat := 4983230072969 + 3 ^ 40 * 2591968 * 2
def baseEnd_2591968 : Nat := 887283616715346764653175

theorem tailTrace_2591968 : CollatzResearch.WordTrace tailWord_2591968 prefixEnd_2591968 887283616715346764653175 := by
  unfold tailWord_2591968
  simp only [CollatzResearch.WordTrace]
  refine ⟨47268419736875041868260279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63024559649166722491013705 47268419736875041868260279)
  ·
    refine ⟨70902629605312562802390419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47268419736875041868260279 70902629605312562802390419)
    ·
      refine ⟨106353944407968844203585629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70902629605312562802390419 106353944407968844203585629)
      ·
        refine ⟨39882729152988316576344611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106353944407968844203585629 39882729152988316576344611)
        ·
          refine ⟨59824093729482474864516917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39882729152988316576344611 59824093729482474864516917)
          ·
            refine ⟨5608508787138982018548461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59824093729482474864516917 5608508787138982018548461)
            ·
              refine ⟨2103190795177118256955673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5608508787138982018548461 2103190795177118256955673)
              ·
                refine ⟨1577393096382838692716755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2103190795177118256955673 1577393096382838692716755)
                ·
                  refine ⟨2366089644574258039075133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1577393096382838692716755 2366089644574258039075133)
                  ·
                    refine ⟨887283616715346764653175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2366089644574258039075133 887283616715346764653175)
                    ·
                      rfl

theorem cell22_2591968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 2, 1, 3].length) (baseStart_2591968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2591968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2591968 prefixEnd_2591968 := by exact prefixLift 2591968
  have htrace : WordTrace (prefixWord ++ tailWord_2591968) baseStart_2591968 baseEnd_2591968 := by
    simpa [prefixWord, tailWord_2591968, baseEnd_2591968] using wordTrace_append hprefix tailTrace_2591968
  have hstable : (prefixWord ++ tailWord_2591968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591968).length < 2 ^ (prefixWord ++ tailWord_2591968).sum := by decide
  have hdescent : baseEnd_2591968 < baseStart_2591968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591981 : List Nat := [1, 5, 1, 2, 2, 1, 4, 1, 5]
def baseStart_2591981 : Nat := 118140960795 + 2591981 * 2 ^ 59
def prefixEnd_2591981 : Nat := 4983230072969 + 3 ^ 40 * 2591981 * 2
def baseEnd_2591981 : Nat := 295762688960339688026045

theorem tailTrace_2591981 : CollatzResearch.WordTrace tailWord_2591981 prefixEnd_2591981 295762688960339688026045 := by
  unfold tailWord_2591981
  simp only [CollatzResearch.WordTrace]
  refine ⟨94537313622702986956743797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63024875748468657971162531 94537313622702986956743797)
  ·
    refine ⟨8862873152128405027194731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94537313622702986956743797 8862873152128405027194731)
    ·
      refine ⟨13294309728192607540792097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8862873152128405027194731 13294309728192607540792097)
      ·
        refine ⟨9970732296144455655594073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13294309728192607540792097 9970732296144455655594073)
        ·
          refine ⟨7478049222108341741695555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9970732296144455655594073 7478049222108341741695555)
          ·
            refine ⟨11217073833162512612543333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7478049222108341741695555 11217073833162512612543333)
            ·
              refine ⟨2103201343717971114851875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11217073833162512612543333 2103201343717971114851875)
              ·
                refine ⟨3154802015576956672277813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2103201343717971114851875 3154802015576956672277813)
                ·
                  refine ⟨295762688960339688026045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3154802015576956672277813 295762688960339688026045)
                  ·
                    rfl

theorem cell22_2591981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_2591981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2591981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2591981 prefixEnd_2591981 := by exact prefixLift 2591981
  have htrace : WordTrace (prefixWord ++ tailWord_2591981) baseStart_2591981 baseEnd_2591981 := by
    simpa [prefixWord, tailWord_2591981, baseEnd_2591981] using wordTrace_append hprefix tailTrace_2591981
  have hstable : (prefixWord ++ tailWord_2591981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591981).length < 2 ^ (prefixWord ++ tailWord_2591981).sum := by decide
  have hdescent : baseEnd_2591981 < baseStart_2591981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592009 : List Nat := [1, 2, 1, 1, 3, 3, 2, 5, 4]
def baseStart_2592009 : Nat := 118140960795 + 2592009 * 2 ^ 59
def prefixEnd_2592009 : Nat := 4983230072969 + 3 ^ 40 * 2592009 * 2
def baseEnd_2592009 : Nat := 295765883951078774792683

theorem tailTrace_2592009 : CollatzResearch.WordTrace tailWord_2592009 prefixEnd_2592009 295765883951078774792683 := by
  unfold tailWord_2592009
  simp only [CollatzResearch.WordTrace]
  refine ⟨94538334866601547738763081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63025556577734365159175387 94538334866601547738763081)
  ·
    refine ⟨70903751149951160804072311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94538334866601547738763081 70903751149951160804072311)
    ·
      refine ⟨106355626724926741206108467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70903751149951160804072311 106355626724926741206108467)
      ·
        refine ⟨159533440087390111809162701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106355626724926741206108467 159533440087390111809162701)
        ·
          refine ⟨59825040032771291928436013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159533440087390111809162701 59825040032771291928436013)
          ·
            refine ⟨22434390012289234473163505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59825040032771291928436013 22434390012289234473163505)
            ·
              refine ⟨16825792509216925854872629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22434390012289234473163505 16825792509216925854872629)
              ·
                refine ⟨1577418047739086798894309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16825792509216925854872629 1577418047739086798894309)
                ·
                  refine ⟨295765883951078774792683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1577418047739086798894309 295765883951078774792683)
                  ·
                    rfl

theorem cell22_2592009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 5, 4].length) (baseStart_2592009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2592009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2592009 prefixEnd_2592009 := by exact prefixLift 2592009
  have htrace : WordTrace (prefixWord ++ tailWord_2592009) baseStart_2592009 baseEnd_2592009 := by
    simpa [prefixWord, tailWord_2592009, baseEnd_2592009] using wordTrace_append hprefix tailTrace_2592009
  have hstable : (prefixWord ++ tailWord_2592009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592009).length < 2 ^ (prefixWord ++ tailWord_2592009).sum := by decide
  have hdescent : baseEnd_2592009 < baseStart_2592009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592011 : List Nat := [1, 1, 1, 1, 5, 4, 3, 1, 1, 4]
def baseStart_2592011 : Nat := 118140960795 + 2592011 * 2 ^ 59
def prefixEnd_2592011 : Nat := 4983230072969 + 3 ^ 40 * 2592011 * 2
def baseEnd_2592011 : Nat := 887298336494108985828043

theorem tailTrace_2592011 : CollatzResearch.WordTrace tailWord_2592011 prefixEnd_2592011 887298336494108985828043 := by
  unfold tailWord_2592011
  simp only [CollatzResearch.WordTrace]
  refine ⟨94538407812594302080335887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63025605208396201386890591 94538407812594302080335887)
  ·
    refine ⟨141807611718891453120503831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94538407812594302080335887 141807611718891453120503831)
    ·
      refine ⟨212711417578337179680755747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141807611718891453120503831 212711417578337179680755747)
      ·
        refine ⟨319067126367505769521133621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212711417578337179680755747 319067126367505769521133621)
        ·
          refine ⟨29912543096953665892606277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 319067126367505769521133621 29912543096953665892606277)
          ·
            refine ⟨5608601830678812354863677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29912543096953665892606277 5608601830678812354863677)
            ·
              refine ⟨2103225686504554633073879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5608601830678812354863677 2103225686504554633073879)
              ·
                refine ⟨3154838529756831949610819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2103225686504554633073879 3154838529756831949610819)
                ·
                  refine ⟨4732257794635247924416229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3154838529756831949610819 4732257794635247924416229)
                  ·
                    refine ⟨887298336494108985828043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4732257794635247924416229 887298336494108985828043)
                    ·
                      rfl

theorem cell22_2592011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 1, 1, 4].length) (baseStart_2592011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2592011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2592011 prefixEnd_2592011 := by exact prefixLift 2592011
  have htrace : WordTrace (prefixWord ++ tailWord_2592011) baseStart_2592011 baseEnd_2592011 := by
    simpa [prefixWord, tailWord_2592011, baseEnd_2592011] using wordTrace_append hprefix tailTrace_2592011
  have hstable : (prefixWord ++ tailWord_2592011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592011).length < 2 ^ (prefixWord ++ tailWord_2592011).sum := by decide
  have hdescent : baseEnd_2592011 < baseStart_2592011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592026 : List Nat := [3, 1, 1, 3, 3, 2, 1, 4, 4]
def baseStart_2592026 : Nat := 118140960795 + 2592026 * 2 ^ 59
def prefixEnd_2592026 : Nat := 4983230072969 + 3 ^ 40 * 2592026 * 2
def baseEnd_2592026 : Nat := 295767823766884648900999

theorem tailTrace_2592026 : CollatzResearch.WordTrace tailWord_2592026 prefixEnd_2592026 295767823766884648900999 := by
  unfold tailWord_2592026
  simp only [CollatzResearch.WordTrace]
  refine ⟨23634738726884989910532983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63025969938359973094754621 23634738726884989910532983)
  ·
    refine ⟨35452108090327484865799475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23634738726884989910532983 35452108090327484865799475)
    ·
      refine ⟨53178162135491227298699213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35452108090327484865799475 53178162135491227298699213)
      ·
        refine ⟨19941810800809210237012205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53178162135491227298699213 19941810800809210237012205)
        ·
          refine ⟨7478179050303453838879577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19941810800809210237012205 7478179050303453838879577)
          ·
            refine ⟨5608634287727590379159683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7478179050303453838879577 5608634287727590379159683)
            ·
              refine ⟨8412951431591385568739525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5608634287727590379159683 8412951431591385568739525)
              ·
                refine ⟨1577428393423384794138661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8412951431591385568739525 1577428393423384794138661)
                ·
                  refine ⟨295767823766884648900999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1577428393423384794138661 295767823766884648900999)
                  ·
                    rfl

theorem cell22_2592026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 4, 4].length) (baseStart_2592026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2592026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2592026 prefixEnd_2592026 := by exact prefixLift 2592026
  have htrace : WordTrace (prefixWord ++ tailWord_2592026) baseStart_2592026 baseEnd_2592026 := by
    simpa [prefixWord, tailWord_2592026, baseEnd_2592026] using wordTrace_append hprefix tailTrace_2592026
  have hstable : (prefixWord ++ tailWord_2592026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592026).length < 2 ^ (prefixWord ++ tailWord_2592026).sum := by decide
  have hdescent : baseEnd_2592026 < baseStart_2592026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592266 : List Nat := [3, 1, 2, 2, 2, 2, 2, 1, 2, 5]
def baseStart_2592266 : Nat := 118140960795 + 2592266 * 2 ^ 59
def prefixEnd_2592266 : Nat := 4983230072969 + 3 ^ 40 * 2592266 * 2
def baseEnd_2592266 : Nat := 887385628205373320702261

theorem tailTrace_2592266 : CollatzResearch.WordTrace tailWord_2592266 prefixEnd_2592266 887385628205373320702261 := by
  unfold tailWord_2592266
  simp only [CollatzResearch.WordTrace]
  refine ⟨23636927106667620157717163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63031805617780320420579101 23636927106667620157717163)
  ·
    refine ⟨35455390660001430236575745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23636927106667620157717163 35455390660001430236575745)
    ·
      refine ⟨26591542995001072677431809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35455390660001430236575745 26591542995001072677431809)
      ·
        refine ⟨19943657246250804508073857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26591542995001072677431809 19943657246250804508073857)
        ·
          refine ⟨14957742934688103381055393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19943657246250804508073857 14957742934688103381055393)
          ·
            refine ⟨11218307201016077535791545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14957742934688103381055393 11218307201016077535791545)
            ·
              refine ⟨8413730400762058151843659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11218307201016077535791545 8413730400762058151843659)
              ·
                refine ⟨12620595601143087227765489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8413730400762058151843659 12620595601143087227765489)
                ·
                  refine ⟨9465446700857315420824117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12620595601143087227765489 9465446700857315420824117)
                  ·
                    refine ⟨887385628205373320702261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9465446700857315420824117 887385628205373320702261)
                    ·
                      rfl

theorem cell22_2592266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_2592266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2592266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2592266 prefixEnd_2592266 := by exact prefixLift 2592266
  have htrace : WordTrace (prefixWord ++ tailWord_2592266) baseStart_2592266 baseEnd_2592266 := by
    simpa [prefixWord, tailWord_2592266, baseEnd_2592266] using wordTrace_append hprefix tailTrace_2592266
  have hstable : (prefixWord ++ tailWord_2592266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592266).length < 2 ^ (prefixWord ++ tailWord_2592266).sum := by decide
  have hdescent : baseEnd_2592266 < baseStart_2592266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592298 : List Nat := [3, 1, 4, 1, 1, 1, 1, 5, 1, 4]
def baseStart_2592298 : Nat := 118140960795 + 2592298 * 2 ^ 59
def prefixEnd_2592298 : Nat := 4983230072969 + 3 ^ 40 * 2592298 * 2
def baseEnd_2592298 : Nat := 887396582459335903902163

theorem tailTrace_2592298 : CollatzResearch.WordTrace tailWord_2592298 prefixEnd_2592298 887396582459335903902163 := by
  unfold tailWord_2592298
  simp only [CollatzResearch.WordTrace]
  refine ⟨23637218890638637524008387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63032583708369700064022365 23637218890638637524008387)
  ·
    refine ⟨35455828335957956286012581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23637218890638637524008387 35455828335957956286012581)
    ·
      refine ⟨6647967812992116803627359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35455828335957956286012581 6647967812992116803627359)
      ·
        refine ⟨9971951719488175205441039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6647967812992116803627359 9971951719488175205441039)
        ·
          refine ⟨14957927579232262808161559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9971951719488175205441039 14957927579232262808161559)
          ·
            refine ⟨22436891368848394212242339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14957927579232262808161559 22436891368848394212242339)
            ·
              refine ⟨33655337053272591318363509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22436891368848394212242339 33655337053272591318363509)
              ·
                refine ⟨3155187848744305436096579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33655337053272591318363509 3155187848744305436096579)
                ·
                  refine ⟨4732781773116458154144869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3155187848744305436096579 4732781773116458154144869)
                  ·
                    refine ⟨887396582459335903902163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4732781773116458154144869 887396582459335903902163)
                    ·
                      rfl

theorem cell22_2592298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_2592298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2592298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2592298 prefixEnd_2592298 := by exact prefixLift 2592298
  have htrace : WordTrace (prefixWord ++ tailWord_2592298) baseStart_2592298 baseEnd_2592298 := by
    simpa [prefixWord, tailWord_2592298, baseEnd_2592298] using wordTrace_append hprefix tailTrace_2592298
  have hstable : (prefixWord ++ tailWord_2592298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592298).length < 2 ^ (prefixWord ++ tailWord_2592298).sum := by decide
  have hdescent : baseEnd_2592298 < baseStart_2592298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592313 : List Nat := [1, 2, 1, 5, 1, 4, 1, 1, 6]
def baseStart_2592313 : Nat := 118140960795 + 2592313 * 2 ^ 59
def prefixEnd_2592313 : Nat := 4983230072969 + 3 ^ 40 * 2592313 * 2
def baseEnd_2592313 : Nat := 295800572421960288259039

theorem tailTrace_2592313 : CollatzResearch.WordTrace tailWord_2592313 prefixEnd_2592313 295800572421960288259039 := by
  unfold tailWord_2592313
  simp only [CollatzResearch.WordTrace]
  refine ⟨94549422657500207657829593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63032948438333471771886395 94549422657500207657829593)
  ·
    refine ⟨70912066993125155743372195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94549422657500207657829593 70912066993125155743372195)
    ·
      refine ⟨106368100489687733615058293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70912066993125155743372195 106368100489687733615058293)
      ·
        refine ⟨9972009420908225026411715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106368100489687733615058293 9972009420908225026411715)
        ·
          refine ⟨14958014131362337539617573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9972009420908225026411715 14958014131362337539617573)
          ·
            refine ⟨2804627649630438288678295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14958014131362337539617573 2804627649630438288678295)
            ·
              refine ⟨4206941474445657433017443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2804627649630438288678295 4206941474445657433017443)
              ·
                refine ⟨6310412211668486149526165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4206941474445657433017443 6310412211668486149526165)
                ·
                  refine ⟨295800572421960288259039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6310412211668486149526165 295800572421960288259039)
                  ·
                    rfl

theorem cell22_2592313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 6].length) (baseStart_2592313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2592313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2592313 prefixEnd_2592313 := by exact prefixLift 2592313
  have htrace : WordTrace (prefixWord ++ tailWord_2592313) baseStart_2592313 baseEnd_2592313 := by
    simpa [prefixWord, tailWord_2592313, baseEnd_2592313] using wordTrace_append hprefix tailTrace_2592313
  have hstable : (prefixWord ++ tailWord_2592313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592313).length < 2 ^ (prefixWord ++ tailWord_2592313).sum := by decide
  have hdescent : baseEnd_2592313 < baseStart_2592313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592343 : List Nat := [1, 1, 3, 2, 2, 4, 2, 1, 2, 4]
def baseStart_2592343 : Nat := 118140960795 + 2592343 * 2 ^ 59
def prefixEnd_2592343 : Nat := 4983230072969 + 3 ^ 40 * 2592343 * 2
def baseEnd_2592343 : Nat := 887411986878970786527025

theorem tailTrace_2592343 : CollatzResearch.WordTrace tailWord_2592343 prefixEnd_2592343 887411986878970786527025 := by
  unfold tailWord_2592343
  simp only [CollatzResearch.WordTrace]
  refine ⟨94550516847391522781421683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63033677898261015187614455 94550516847391522781421683)
  ·
    refine ⟨141825775271087284172132525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94550516847391522781421683 141825775271087284172132525)
    ·
      refine ⟨53184665726657731564549697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141825775271087284172132525 53184665726657731564549697)
      ·
        refine ⟨39888499294993298673412273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53184665726657731564549697 39888499294993298673412273)
        ·
          refine ⟨29916374471244974005059205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39888499294993298673412273 29916374471244974005059205)
          ·
            refine ⟨5609320213358432625948601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29916374471244974005059205 5609320213358432625948601)
            ·
              refine ⟨4206990160018824469461451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5609320213358432625948601 4206990160018824469461451)
              ·
                refine ⟨6310485240028236704192177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4206990160018824469461451 6310485240028236704192177)
                ·
                  refine ⟨4732863930021177528144133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6310485240028236704192177 4732863930021177528144133)
                  ·
                    refine ⟨887411986878970786527025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4732863930021177528144133 887411986878970786527025)
                    ·
                      rfl

theorem cell22_2592343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 2, 4].length) (baseStart_2592343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2592343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2592343 prefixEnd_2592343 := by exact prefixLift 2592343
  have htrace : WordTrace (prefixWord ++ tailWord_2592343) baseStart_2592343 baseEnd_2592343 := by
    simpa [prefixWord, tailWord_2592343, baseEnd_2592343] using wordTrace_append hprefix tailTrace_2592343
  have hstable : (prefixWord ++ tailWord_2592343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592343).length < 2 ^ (prefixWord ++ tailWord_2592343).sum := by decide
  have hdescent : baseEnd_2592343 < baseStart_2592343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592349 : List Nat := [1, 4, 4, 2, 1, 1, 3, 1, 1, 4]
def baseStart_2592349 : Nat := 118140960795 + 2592349 * 2 ^ 59
def prefixEnd_2592349 : Nat := 4983230072969 + 3 ^ 40 * 2592349 * 2
def baseEnd_2592349 : Nat := 887414040801588770877007

theorem tailTrace_2592349 : CollatzResearch.WordTrace tailWord_2592349 prefixEnd_2592349 887414040801588770877007 := by
  unfold tailWord_2592349
  simp only [CollatzResearch.WordTrace]
  refine ⟨94550735685369785806140101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63033823790246523870760067 94550735685369785806140101)
  ·
    refine ⟨17728262941006834838651269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94550735685369785806140101 17728262941006834838651269)
    ·
      refine ⟨3324049301438781532247113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17728262941006834838651269 3324049301438781532247113)
      ·
        refine ⟨2493036976079086149185335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3324049301438781532247113 2493036976079086149185335)
        ·
          refine ⟨3739555464118629223778003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2493036976079086149185335 3739555464118629223778003)
          ·
            refine ⟨5609333196177943835667005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3739555464118629223778003 5609333196177943835667005)
            ·
              refine ⟨2103499948566728938375127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5609333196177943835667005 2103499948566728938375127)
              ·
                refine ⟨3155249922850093407562691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2103499948566728938375127 3155249922850093407562691)
                ·
                  refine ⟨4732874884275140111344037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3155249922850093407562691 4732874884275140111344037)
                  ·
                    refine ⟨887414040801588770877007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4732874884275140111344037 887414040801588770877007)
                    ·
                      rfl

theorem cell22_2592349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_2592349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2592349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2592349 prefixEnd_2592349 := by exact prefixLift 2592349
  have htrace : WordTrace (prefixWord ++ tailWord_2592349) baseStart_2592349 baseEnd_2592349 := by
    simpa [prefixWord, tailWord_2592349, baseEnd_2592349] using wordTrace_append hprefix tailTrace_2592349
  have hstable : (prefixWord ++ tailWord_2592349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592349).length < 2 ^ (prefixWord ++ tailWord_2592349).sum := by decide
  have hdescent : baseEnd_2592349 < baseStart_2592349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592407 : List Nat := [1, 1, 3, 3, 2, 3, 2, 3, 1, 3]
def baseStart_2592407 : Nat := 118140960795 + 2592407 * 2 ^ 59
def prefixEnd_2592407 : Nat := 4983230072969 + 3 ^ 40 * 2592407 * 2
def baseEnd_2592407 : Nat := 887433895386895952926829

theorem tailTrace_2592407 : CollatzResearch.WordTrace tailWord_2592407 prefixEnd_2592407 887433895386895952926829 := by
  unfold tailWord_2592407
  simp only [CollatzResearch.WordTrace]
  refine ⟨94552851119159661711751475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63035234079439774474500983 94552851119159661711751475)
  ·
    refine ⟨141829276678739492567627213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94552851119159661711751475 141829276678739492567627213)
    ·
      refine ⟨53185978754527309712860205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141829276678739492567627213 53185978754527309712860205)
      ·
        refine ⟨19944742032947741142322577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53185978754527309712860205 19944742032947741142322577)
        ·
          refine ⟨14958556524710805856741933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19944742032947741142322577 14958556524710805856741933)
          ·
            refine ⟨5609458696766552196278225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14958556524710805856741933 5609458696766552196278225)
            ·
              refine ⟨4207094022574914147208669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5609458696766552196278225 4207094022574914147208669)
              ·
                refine ⟨1577660258465592805203251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4207094022574914147208669 1577660258465592805203251)
                ·
                  refine ⟨2366490387698389207804877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1577660258465592805203251 2366490387698389207804877)
                  ·
                    refine ⟨887433895386895952926829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2366490387698389207804877 887433895386895952926829)
                    ·
                      rfl

theorem cell22_2592407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 3, 1, 3].length) (baseStart_2592407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2592407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2592407 prefixEnd_2592407 := by exact prefixLift 2592407
  have htrace : WordTrace (prefixWord ++ tailWord_2592407) baseStart_2592407 baseEnd_2592407 := by
    simpa [prefixWord, tailWord_2592407, baseEnd_2592407] using wordTrace_append hprefix tailTrace_2592407
  have hstable : (prefixWord ++ tailWord_2592407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592407).length < 2 ^ (prefixWord ++ tailWord_2592407).sum := by decide
  have hdescent : baseEnd_2592407 < baseStart_2592407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592420 : List Nat := [2, 3, 1, 2, 2, 4, 1, 2, 5]
def baseStart_2592420 : Nat := 118140960795 + 2592420 * 2 ^ 59
def prefixEnd_2592420 : Nat := 4983230072969 + 3 ^ 40 * 2592420 * 2
def baseEnd_2592420 : Nat := 295812781850856084117263

theorem tailTrace_2592420 : CollatzResearch.WordTrace tailWord_2592420 prefixEnd_2592420 295812781850856084117263 := by
  unfold tailWord_2592420
  simp only [CollatzResearch.WordTrace]
  refine ⟨47276662634056282465987357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63035550178741709954649809 47276662634056282465987357)
  ·
    refine ⟨17728748487771105924745259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47276662634056282465987357 17728748487771105924745259)
    ·
      refine ⟨26593122731656658887117889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17728748487771105924745259 26593122731656658887117889)
      ·
        refine ⟨19944842048742494165338417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26593122731656658887117889 19944842048742494165338417)
        ·
          refine ⟨14958631536556870624003813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19944842048742494165338417 14958631536556870624003813)
          ·
            refine ⟨2804743413104413242000715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14958631536556870624003813 2804743413104413242000715)
            ·
              refine ⟨4207115119656619863001073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2804743413104413242000715 4207115119656619863001073)
              ·
                refine ⟨3155336339742464897250805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4207115119656619863001073 3155336339742464897250805)
                ·
                  refine ⟨295812781850856084117263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3155336339742464897250805 295812781850856084117263)
                  ·
                    rfl

theorem cell22_2592420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 2, 5].length) (baseStart_2592420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2592420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2592420 prefixEnd_2592420 := by exact prefixLift 2592420
  have htrace : WordTrace (prefixWord ++ tailWord_2592420) baseStart_2592420 baseEnd_2592420 := by
    simpa [prefixWord, tailWord_2592420, baseEnd_2592420] using wordTrace_append hprefix tailTrace_2592420
  have hstable : (prefixWord ++ tailWord_2592420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592420).length < 2 ^ (prefixWord ++ tailWord_2592420).sum := by decide
  have hdescent : baseEnd_2592420 < baseStart_2592420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592437 : List Nat := [1, 3, 3, 3, 2, 1, 3, 1, 5]
def baseStart_2592437 : Nat := 118140960795 + 2592437 * 2 ^ 59
def prefixEnd_2592437 : Nat := 4983230072969 + 3 ^ 40 * 2592437 * 2
def baseEnd_2592437 : Nat := 295814721666661958225579

theorem tailTrace_2592437 : CollatzResearch.WordTrace tailWord_2592437 prefixEnd_2592437 295814721666661958225579 := by
  unfold tailWord_2592437
  simp only [CollatzResearch.WordTrace]
  refine ⟨94553945309050976835343565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63035963539367317890229043 94553945309050976835343565)
  ·
    refine ⟨35457729490894116313253837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94553945309050976835343565 35457729490894116313253837)
    ·
      refine ⟨13296648559085293617470189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35457729490894116313253837 13296648559085293617470189)
      ·
        refine ⟨4986243209656985106551321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13296648559085293617470189 4986243209656985106551321)
        ·
          refine ⟨3739682407242738829913491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4986243209656985106551321 3739682407242738829913491)
          ·
            refine ⟨5609523610864108244870237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3739682407242738829913491 5609523610864108244870237)
            ·
              refine ⟨2103571354074040591826339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5609523610864108244870237 2103571354074040591826339)
              ·
                refine ⟨3155357031111060887739509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2103571354074040591826339 3155357031111060887739509)
                ·
                  refine ⟨295814721666661958225579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3155357031111060887739509 295814721666661958225579)
                  ·
                    rfl

theorem cell22_2592437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 1, 5].length) (baseStart_2592437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2592437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2592437 prefixEnd_2592437 := by exact prefixLift 2592437
  have htrace : WordTrace (prefixWord ++ tailWord_2592437) baseStart_2592437 baseEnd_2592437 := by
    simpa [prefixWord, tailWord_2592437, baseEnd_2592437] using wordTrace_append hprefix tailTrace_2592437
  have hstable : (prefixWord ++ tailWord_2592437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592437).length < 2 ^ (prefixWord ++ tailWord_2592437).sum := by decide
  have hdescent : baseEnd_2592437 < baseStart_2592437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592465 : List Nat := [1, 2, 2, 1, 2, 4, 3, 3, 4]
def baseStart_2592465 : Nat := 118140960795 + 2592465 * 2 ^ 59
def prefixEnd_2592465 : Nat := 4983230072969 + 3 ^ 40 * 2592465 * 2
def baseEnd_2592465 : Nat := 295817916657401044992217

theorem tailTrace_2592465 : CollatzResearch.WordTrace tailWord_2592465 prefixEnd_2592465 295817916657401044992217 := by
  unfold tailWord_2592465
  simp only [CollatzResearch.WordTrace]
  refine ⟨94554966552949537617362849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63036644368633025078241899 94554966552949537617362849)
  ·
    refine ⟨70916224914712153213022137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94554966552949537617362849 70916224914712153213022137)
    ·
      refine ⟨53187168686034114909766603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70916224914712153213022137 53187168686034114909766603)
      ·
        refine ⟨79780753029051172364649905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53187168686034114909766603 79780753029051172364649905)
        ·
          refine ⟨59835564771788379273487429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79780753029051172364649905 59835564771788379273487429)
          ·
            refine ⟨11219168394710321113778893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59835564771788379273487429 11219168394710321113778893)
            ·
              refine ⟨4207188148016370417667085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11219168394710321113778893 4207188148016370417667085)
              ·
                refine ⟨1577695555506138906625157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4207188148016370417667085 1577695555506138906625157)
                ·
                  refine ⟨295817916657401044992217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1577695555506138906625157 295817916657401044992217)
                  ·
                    rfl

theorem cell22_2592465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 3, 4].length) (baseStart_2592465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2592465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2592465 prefixEnd_2592465 := by exact prefixLift 2592465
  have htrace : WordTrace (prefixWord ++ tailWord_2592465) baseStart_2592465 baseEnd_2592465 := by
    simpa [prefixWord, tailWord_2592465, baseEnd_2592465] using wordTrace_append hprefix tailTrace_2592465
  have hstable : (prefixWord ++ tailWord_2592465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592465).length < 2 ^ (prefixWord ++ tailWord_2592465).sum := by decide
  have hdescent : baseEnd_2592465 < baseStart_2592465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592493 : List Nat := [1, 5, 1, 2, 1, 2, 1, 9]
def baseStart_2592493 : Nat := 118140960795 + 2592493 * 2 ^ 59
def prefixEnd_2592493 : Nat := 4983230072969 + 3 ^ 40 * 2592493 * 2
def baseEnd_2592493 : Nat := 98607037216046710586285

theorem tailTrace_2592493 : CollatzResearch.WordTrace tailWord_2592493 prefixEnd_2592493 98607037216046710586285 := by
  unfold tailWord_2592493
  simp only [CollatzResearch.WordTrace]
  refine ⟨94555987796848098399382133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63037325197898732266254755 94555987796848098399382133)
  ·
    refine ⟨8864623855954509224942075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94555987796848098399382133 8864623855954509224942075)
    ·
      refine ⟨13296935783931763837413113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8864623855954509224942075 13296935783931763837413113)
      ·
        refine ⟨9972701837948822878059835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13296935783931763837413113 9972701837948822878059835)
        ·
          refine ⟨14959052756923234317089753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9972701837948822878059835 14959052756923234317089753)
          ·
            refine ⟨11219289567692425737817315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14959052756923234317089753 11219289567692425737817315)
            ·
              refine ⟨16828934351538638606725973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11219289567692425737817315 16828934351538638606725973)
              ·
                refine ⟨98607037216046710586285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16828934351538638606725973 98607037216046710586285)
                ·
                  rfl

theorem cell22_2592493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 9].length) (baseStart_2592493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2592493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2592493 prefixEnd_2592493 := by exact prefixLift 2592493
  have htrace : WordTrace (prefixWord ++ tailWord_2592493) baseStart_2592493 baseEnd_2592493 := by
    simpa [prefixWord, tailWord_2592493, baseEnd_2592493] using wordTrace_append hprefix tailTrace_2592493
  have hstable : (prefixWord ++ tailWord_2592493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592493).length < 2 ^ (prefixWord ++ tailWord_2592493).sum := by decide
  have hdescent : baseEnd_2592493 < baseStart_2592493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592497 : List Nat := [1, 2, 2, 2, 2, 3, 4, 1, 2, 3]
def baseStart_2592497 : Nat := 118140960795 + 2592497 * 2 ^ 59
def prefixEnd_2592497 : Nat := 4983230072969 + 3 ^ 40 * 2592497 * 2
def baseEnd_2592497 : Nat := 887464704226165718176553

theorem tailTrace_2592497 : CollatzResearch.WordTrace tailWord_2592497 prefixEnd_2592497 887464704226165718176553 := by
  unfold tailWord_2592497
  simp only [CollatzResearch.WordTrace]
  refine ⟨94556133688833607082527745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63037422459222404721685163 94556133688833607082527745)
  ·
    refine ⟨70917100266625205311895809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94556133688833607082527745 70917100266625205311895809)
    ·
      refine ⟨53187825199968903983921857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70917100266625205311895809 53187825199968903983921857)
      ·
        refine ⟨39890868899976677987941393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53187825199968903983921857 39890868899976677987941393)
        ·
          refine ⟨29918151674982508490956045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39890868899976677987941393 29918151674982508490956045)
          ·
            refine ⟨11219306878118440684108517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29918151674982508490956045 11219306878118440684108517)
            ·
              refine ⟨2103620039647207628270347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11219306878118440684108517 2103620039647207628270347)
              ·
                refine ⟨3155430059470811442405521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2103620039647207628270347 3155430059470811442405521)
                ·
                  refine ⟨2366572544603108581804141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3155430059470811442405521 2366572544603108581804141)
                  ·
                    refine ⟨887464704226165718176553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2366572544603108581804141 887464704226165718176553)
                    ·
                      rfl

theorem cell22_2592497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 1, 2, 3].length) (baseStart_2592497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2592497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2592497 prefixEnd_2592497 := by exact prefixLift 2592497
  have htrace : WordTrace (prefixWord ++ tailWord_2592497) baseStart_2592497 baseEnd_2592497 := by
    simpa [prefixWord, tailWord_2592497, baseEnd_2592497] using wordTrace_append hprefix tailTrace_2592497
  have hstable : (prefixWord ++ tailWord_2592497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592497).length < 2 ^ (prefixWord ++ tailWord_2592497).sum := by decide
  have hdescent : baseEnd_2592497 < baseStart_2592497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592585 : List Nat := [1, 2, 1, 1, 2, 4, 3, 3, 1, 4]
def baseStart_2592585 : Nat := 118140960795 + 2592585 * 2 ^ 59
def prefixEnd_2592585 : Nat := 4983230072969 + 3 ^ 40 * 2592585 * 2
def baseEnd_2592585 : Nat := 887494828424562821976283

theorem tailTrace_2592585 : CollatzResearch.WordTrace tailWord_2592585 prefixEnd_2592585 887494828424562821976283 := by
  unfold tailWord_2592585
  simp only [CollatzResearch.WordTrace]
  refine ⟨94559343312514798111731209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63039562208343198741154139 94559343312514798111731209)
  ·
    refine ⟨70919507484386098583798407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94559343312514798111731209 70919507484386098583798407)
    ·
      refine ⟨106379261226579147875697611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70919507484386098583798407 106379261226579147875697611)
      ·
        refine ⟨159568891839868721813546417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106379261226579147875697611 159568891839868721813546417)
        ·
          refine ⟨119676668879901541360159813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159568891839868721813546417 119676668879901541360159813)
          ·
            refine ⟨22439375414981539005029965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119676668879901541360159813 22439375414981539005029965)
            ·
              refine ⟨8414765780618077126886237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22439375414981539005029965 8414765780618077126886237)
              ·
                refine ⟨3155537167731778922582339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8414765780618077126886237 3155537167731778922582339)
                ·
                  refine ⟨4733305751597668383873509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3155537167731778922582339 4733305751597668383873509)
                  ·
                    refine ⟨887494828424562821976283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4733305751597668383873509 887494828424562821976283)
                    ·
                      rfl

theorem cell22_2592585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 3, 1, 4].length) (baseStart_2592585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2592585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2592585 prefixEnd_2592585 := by exact prefixLift 2592585
  have htrace : WordTrace (prefixWord ++ tailWord_2592585) baseStart_2592585 baseEnd_2592585 := by
    simpa [prefixWord, tailWord_2592585, baseEnd_2592585] using wordTrace_append hprefix tailTrace_2592585
  have hstable : (prefixWord ++ tailWord_2592585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592585).length < 2 ^ (prefixWord ++ tailWord_2592585).sum := by decide
  have hdescent : baseEnd_2592585 < baseStart_2592585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592589 : List Nat := [1, 6, 1, 2, 1, 3, 1, 2, 5]
def baseStart_2592589 : Nat := 118140960795 + 2592589 * 2 ^ 59
def prefixEnd_2592589 : Nat := 4983230072969 + 3 ^ 40 * 2592589 * 2
def baseEnd_2592589 : Nat := 295832065902102714958757

theorem tailTrace_2592589 : CollatzResearch.WordTrace tailWord_2592589 prefixEnd_2592589 295832065902102714958757 := by
  unfold tailWord_2592589
  simp only [CollatzResearch.WordTrace]
  refine ⟨94559489204500306794876821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63039659469666871196584547 94559489204500306794876821)
  ·
    refine ⟨4432476056460951881009851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 94559489204500306794876821 4432476056460951881009851)
    ·
      refine ⟨6648714084691427821514777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4432476056460951881009851 6648714084691427821514777)
      ·
        refine ⟨4986535563518570866136083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6648714084691427821514777 4986535563518570866136083)
        ·
          refine ⟨7479803345277856299204125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4986535563518570866136083 7479803345277856299204125)
          ·
            refine ⟨2804926254479196112201547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7479803345277856299204125 2804926254479196112201547)
            ·
              refine ⟨4207389381718794168302321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2804926254479196112201547 4207389381718794168302321)
              ·
                refine ⟨3155542036289095626226741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4207389381718794168302321 3155542036289095626226741)
                ·
                  refine ⟨295832065902102714958757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3155542036289095626226741 295832065902102714958757)
                  ·
                    rfl

theorem cell22_2592589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_2592589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2592589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2592589 prefixEnd_2592589 := by exact prefixLift 2592589
  have htrace : WordTrace (prefixWord ++ tailWord_2592589) baseStart_2592589 baseEnd_2592589 := by
    simpa [prefixWord, tailWord_2592589, baseEnd_2592589] using wordTrace_append hprefix tailTrace_2592589
  have hstable : (prefixWord ++ tailWord_2592589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592589).length < 2 ^ (prefixWord ++ tailWord_2592589).sum := by decide
  have hdescent : baseEnd_2592589 < baseStart_2592589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592647 : List Nat := [1, 1, 4, 2, 4, 1, 1, 2, 2, 4]
def baseStart_2592647 : Nat := 118140960795 + 2592647 * 2 ^ 59
def prefixEnd_2592647 : Nat := 4983230072969 + 3 ^ 40 * 2592647 * 2
def baseEnd_2592647 : Nat := 887516052291615326926093

theorem tailTrace_2592647 : CollatzResearch.WordTrace tailWord_2592647 prefixEnd_2592647 887516052291615326926093 := by
  unfold tailWord_2592647
  simp only [CollatzResearch.WordTrace]
  refine ⟨94561604638290182700488195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63041069758860121800325463 94561604638290182700488195)
  ·
    refine ⟨141842406957435274050732293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94561604638290182700488195 141842406957435274050732293)
    ·
      refine ⟨26595451304519113884512305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141842406957435274050732293 26595451304519113884512305)
      ·
        refine ⟨19946588478389335413384229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26595451304519113884512305 19946588478389335413384229)
        ·
          refine ⟨3739985339698000390009543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19946588478389335413384229 3739985339698000390009543)
          ·
            refine ⟨5609978009547000585014315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3739985339698000390009543 5609978009547000585014315)
            ·
              refine ⟨8414967014320500877521473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5609978009547000585014315 8414967014320500877521473)
              ·
                refine ⟨6311225260740375658141105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8414967014320500877521473 6311225260740375658141105)
                ·
                  refine ⟨4733418945555281743605829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6311225260740375658141105 4733418945555281743605829)
                  ·
                    refine ⟨887516052291615326926093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4733418945555281743605829 887516052291615326926093)
                    ·
                      rfl

theorem cell22_2592647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_2592647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2592647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2592647 prefixEnd_2592647 := by exact prefixLift 2592647
  have htrace : WordTrace (prefixWord ++ tailWord_2592647) baseStart_2592647 baseEnd_2592647 := by
    simpa [prefixWord, tailWord_2592647, baseEnd_2592647] using wordTrace_append hprefix tailTrace_2592647
  have hstable : (prefixWord ++ tailWord_2592647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592647).length < 2 ^ (prefixWord ++ tailWord_2592647).sum := by decide
  have hdescent : baseEnd_2592647 < baseStart_2592647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592666 : List Nat := [3, 1, 1, 4, 2, 3, 2, 1, 2, 3]
def baseStart_2592666 : Nat := 118140960795 + 2592666 * 2 ^ 59
def prefixEnd_2592666 : Nat := 4983230072969 + 3 ^ 40 * 2592666 * 2
def baseEnd_2592666 : Nat := 887522556379905610701035

theorem tailTrace_2592666 : CollatzResearch.WordTrace tailWord_2592666 prefixEnd_2592666 887522556379905610701035 := by
  unfold tailWord_2592666
  simp only [CollatzResearch.WordTrace]
  refine ⟨23640574406305337236357463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63041531750147565963619901 23640574406305337236357463)
  ·
    refine ⟨35460861609458005854536195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23640574406305337236357463 35460861609458005854536195)
    ·
      refine ⟨53191292414187008781804293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35460861609458005854536195 53191292414187008781804293)
      ·
        refine ⟨9973367327660064146588305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53191292414187008781804293 9973367327660064146588305)
        ·
          refine ⟨7480025495745048109941229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9973367327660064146588305 7480025495745048109941229)
          ·
            refine ⟨2805009560904393041227961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7480025495745048109941229 2805009560904393041227961)
            ·
              refine ⟨2103757170678294780920971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2805009560904393041227961 2103757170678294780920971)
              ·
                refine ⟨3155635756017442171381457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2103757170678294780920971 3155635756017442171381457)
                ·
                  refine ⟨2366726817013081628536093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3155635756017442171381457 2366726817013081628536093)
                  ·
                    refine ⟨887522556379905610701035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2366726817013081628536093 887522556379905610701035)
                    ·
                      rfl

theorem cell22_2592666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 1, 2, 3].length) (baseStart_2592666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2592666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2592666 prefixEnd_2592666 := by exact prefixLift 2592666
  have htrace : WordTrace (prefixWord ++ tailWord_2592666) baseStart_2592666 baseEnd_2592666 := by
    simpa [prefixWord, tailWord_2592666, baseEnd_2592666] using wordTrace_append hprefix tailTrace_2592666
  have hstable : (prefixWord ++ tailWord_2592666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592666).length < 2 ^ (prefixWord ++ tailWord_2592666).sum := by decide
  have hdescent : baseEnd_2592666 < baseStart_2592666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592720 : List Nat := [2, 1, 1, 1, 1, 2, 5, 2, 3, 4]
def baseStart_2592720 : Nat := 118140960795 + 2592720 * 2 ^ 59
def prefixEnd_2592720 : Nat := 4983230072969 + 3 ^ 40 * 2592720 * 2
def baseEnd_2592720 : Nat := 887541041683467469850869

theorem tailTrace_2592720 : CollatzResearch.WordTrace tailWord_2592720 prefixEnd_2592720 887541041683467469850869 := by
  unfold tailWord_2592720
  simp only [CollatzResearch.WordTrace]
  refine ⟨47282133583512858083947807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63042844778017144111930409 47282133583512858083947807)
  ·
    refine ⟨70923200375269287125921711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47282133583512858083947807 70923200375269287125921711)
    ·
      refine ⟨106384800562903930688882567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70923200375269287125921711 106384800562903930688882567)
      ·
        refine ⟨159577200844355896033323851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106384800562903930688882567 159577200844355896033323851)
        ·
          refine ⟨239365801266533844049985777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159577200844355896033323851 239365801266533844049985777)
          ·
            refine ⟨179524350949900383037489333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 239365801266533844049985777 179524350949900383037489333)
            ·
              refine ⟨16830407901553160909764625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 179524350949900383037489333 16830407901553160909764625)
              ·
                refine ⟨12622805926164870682323469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16830407901553160909764625 12622805926164870682323469)
                ·
                  refine ⟨4733552222311826505871301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12622805926164870682323469 4733552222311826505871301)
                  ·
                    refine ⟨887541041683467469850869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4733552222311826505871301 887541041683467469850869)
                    ·
                      rfl

theorem cell22_2592720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 3, 4].length) (baseStart_2592720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2592720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2592720 prefixEnd_2592720 := by exact prefixLift 2592720
  have htrace : WordTrace (prefixWord ++ tailWord_2592720) baseStart_2592720 baseEnd_2592720 := by
    simpa [prefixWord, tailWord_2592720, baseEnd_2592720] using wordTrace_append hprefix tailTrace_2592720
  have hstable : (prefixWord ++ tailWord_2592720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592720).length < 2 ^ (prefixWord ++ tailWord_2592720).sum := by decide
  have hdescent : baseEnd_2592720 < baseStart_2592720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592735 : List Nat := [1, 1, 2, 3, 4, 1, 1, 1, 8]
def baseStart_2592735 : Nat := 118140960795 + 2592735 * 2 ^ 59
def prefixEnd_2592735 : Nat := 4983230072969 + 3 ^ 40 * 2592735 * 2
def baseEnd_2592735 : Nat := 295848725496670810241941

theorem tailTrace_2592735 : CollatzResearch.WordTrace tailWord_2592735 prefixEnd_2592735 295848725496670810241941 := by
  unfold tailWord_2592735
  simp only [CollatzResearch.WordTrace]
  refine ⟨94564814261971373729691659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63043209507980915819794439 94564814261971373729691659)
  ·
    refine ⟨141847221392957060594537489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94564814261971373729691659 141847221392957060594537489)
    ·
      refine ⟨106385416044717795445903117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141847221392957060594537489 106385416044717795445903117)
      ·
        refine ⟨39894531016769173292213669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106385416044717795445903117 39894531016769173292213669)
        ·
          refine ⟨7480224565644219992290063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39894531016769173292213669 7480224565644219992290063)
          ·
            refine ⟨11220336848466329988435095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7480224565644219992290063 11220336848466329988435095)
            ·
              refine ⟨16830505272699494982652643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11220336848466329988435095 16830505272699494982652643)
              ·
                refine ⟨25245757909049242473978965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16830505272699494982652643 25245757909049242473978965)
                ·
                  refine ⟨295848725496670810241941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25245757909049242473978965 295848725496670810241941)
                  ·
                    rfl

theorem cell22_2592735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 8].length) (baseStart_2592735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2592735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2592735 prefixEnd_2592735 := by exact prefixLift 2592735
  have htrace : WordTrace (prefixWord ++ tailWord_2592735) baseStart_2592735 baseEnd_2592735 := by
    simpa [prefixWord, tailWord_2592735, baseEnd_2592735] using wordTrace_append hprefix tailTrace_2592735
  have hstable : (prefixWord ++ tailWord_2592735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592735).length < 2 ^ (prefixWord ++ tailWord_2592735).sum := by decide
  have hdescent : baseEnd_2592735 < baseStart_2592735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592752 : List Nat := [2, 1, 1, 1, 3, 2, 3, 5, 4]
def baseStart_2592752 : Nat := 118140960795 + 2592752 * 2 ^ 59
def prefixEnd_2592752 : Nat := 4983230072969 + 3 ^ 40 * 2592752 * 2
def baseEnd_2592752 : Nat := 295850665312476684350257

theorem tailTrace_2592752 : CollatzResearch.WordTrace tailWord_2592752 prefixEnd_2592752 295850665312476684350257 := by
  unfold tailWord_2592752
  simp only [CollatzResearch.WordTrace]
  refine ⟨47282717151454892816530255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63043622868606523755373673 47282717151454892816530255)
  ·
    refine ⟨70924075727182339224795383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47282717151454892816530255 70924075727182339224795383)
    ·
      refine ⟨106386113590773508837193075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70924075727182339224795383 106386113590773508837193075)
      ·
        refine ⟨159579170386160263255789613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106386113590773508837193075 159579170386160263255789613)
        ·
          refine ⟨59842188894810098720921105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159579170386160263255789613 59842188894810098720921105)
          ·
            refine ⟨44881641671107574040690829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59842188894810098720921105 44881641671107574040690829)
            ·
              refine ⟨16830615626665340265259061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44881641671107574040690829 16830615626665340265259061)
              ·
                refine ⟨1577870214999875649868037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16830615626665340265259061 1577870214999875649868037)
                ·
                  refine ⟨295850665312476684350257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1577870214999875649868037 295850665312476684350257)
                  ·
                    rfl

theorem cell22_2592752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 5, 4].length) (baseStart_2592752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2592752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2592752 prefixEnd_2592752 := by exact prefixLift 2592752
  have htrace : WordTrace (prefixWord ++ tailWord_2592752) baseStart_2592752 baseEnd_2592752 := by
    simpa [prefixWord, tailWord_2592752, baseEnd_2592752] using wordTrace_append hprefix tailTrace_2592752
  have hstable : (prefixWord ++ tailWord_2592752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592752).length < 2 ^ (prefixWord ++ tailWord_2592752).sum := by decide
  have hdescent : baseEnd_2592752 < baseStart_2592752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592780 : List Nat := [2, 2, 1, 2, 3, 1, 2, 9]
def baseStart_2592780 : Nat := 118140960795 + 2592780 * 2 ^ 59
def prefixEnd_2592780 : Nat := 4983230072969 + 3 ^ 40 * 2592780 * 2
def baseEnd_2592780 : Nat := 98617953434405257038965

theorem tailTrace_2592780 : CollatzResearch.WordTrace tailWord_2592780 prefixEnd_2592780 98617953434405257038965 := by
  unfold tailWord_2592780
  simp only [CollatzResearch.WordTrace]
  refine ⟨47283227773404173207539897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63044303697872230943386529 47283227773404173207539897)
  ·
    refine ⟨35462420830053129905654923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47283227773404173207539897 35462420830053129905654923)
    ·
      refine ⟨53193631245079694858482385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35462420830053129905654923 53193631245079694858482385)
      ·
        refine ⟨39895223433809771143861789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53193631245079694858482385 39895223433809771143861789)
        ·
          refine ⟨14960708787678664178948171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39895223433809771143861789 14960708787678664178948171)
          ·
            refine ⟨22441063181517996268422257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14960708787678664178948171 22441063181517996268422257)
            ·
              refine ⟨16830797386138497201316693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22441063181517996268422257 16830797386138497201316693)
              ·
                refine ⟨98617953434405257038965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16830797386138497201316693 98617953434405257038965)
                ·
                  rfl

theorem cell22_2592780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 9].length) (baseStart_2592780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2592780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2592780 prefixEnd_2592780 := by exact prefixLift 2592780
  have htrace : WordTrace (prefixWord ++ tailWord_2592780) baseStart_2592780 baseEnd_2592780 := by
    simpa [prefixWord, tailWord_2592780, baseEnd_2592780] using wordTrace_append hprefix tailTrace_2592780
  have hstable : (prefixWord ++ tailWord_2592780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592780).length < 2 ^ (prefixWord ++ tailWord_2592780).sum := by decide
  have hdescent : baseEnd_2592780 < baseStart_2592780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592788 : List Nat := [2, 4, 3, 2, 1, 1, 2, 2, 1, 4]
def baseStart_2592788 : Nat := 118140960795 + 2592788 * 2 ^ 59
def prefixEnd_2592788 : Nat := 4983230072969 + 3 ^ 40 * 2592788 * 2
def baseEnd_2592788 : Nat := 887564319473137959150661

theorem tailTrace_2592788 : CollatzResearch.WordTrace tailWord_2592788 prefixEnd_2592788 887564319473137959150661 := by
  unfold tailWord_2592788
  simp only [CollatzResearch.WordTrace]
  refine ⟨47283373665389681890685509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63044498220519575854247345 47283373665389681890685509)
  ·
    refine ⟨8865632562260565354503533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47283373665389681890685509 8865632562260565354503533)
    ·
      refine ⟨3324612210847712007938825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8865632562260565354503533 3324612210847712007938825)
      ·
        refine ⟨2493459158135784005954119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3324612210847712007938825 2493459158135784005954119)
        ·
          refine ⟨3740188737203676008931179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2493459158135784005954119 3740188737203676008931179)
          ·
            refine ⟨5610283105805514013396769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3740188737203676008931179 5610283105805514013396769)
            ·
              refine ⟨4207712329354135510047577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5610283105805514013396769 4207712329354135510047577)
              ·
                refine ⟨3155784247015601632535683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4207712329354135510047577 3155784247015601632535683)
                ·
                  refine ⟨4733676370523402448803525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3155784247015601632535683 4733676370523402448803525)
                  ·
                    refine ⟨887564319473137959150661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4733676370523402448803525 887564319473137959150661)
                    ·
                      rfl

theorem cell22_2592788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_2592788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2592788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2592788 prefixEnd_2592788 := by exact prefixLift 2592788
  have htrace : WordTrace (prefixWord ++ tailWord_2592788) baseStart_2592788 baseEnd_2592788 := by
    simpa [prefixWord, tailWord_2592788, baseEnd_2592788] using wordTrace_append hprefix tailTrace_2592788
  have hstable : (prefixWord ++ tailWord_2592788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592788).length < 2 ^ (prefixWord ++ tailWord_2592788).sum := by decide
  have hdescent : baseEnd_2592788 < baseStart_2592788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592797 : List Nat := [1, 4, 2, 2, 2, 2, 1, 8]
def baseStart_2592797 : Nat := 118140960795 + 2592797 * 2 ^ 59
def prefixEnd_2592797 : Nat := 4983230072969 + 3 ^ 40 * 2592797 * 2
def baseEnd_2592797 : Nat := 98618600039673881741737

theorem tailTrace_2592797 : CollatzResearch.WordTrace tailWord_2592797 prefixEnd_2592797 98618600039673881741737 := by
  unfold tailWord_2592797
  simp only [CollatzResearch.WordTrace]
  refine ⟨94567075587746758318448645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63044717058497838878965763 94567075587746758318448645)
  ·
    refine ⟨17731326672702517184709121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94567075587746758318448645 17731326672702517184709121)
    ·
      refine ⟨13298495004526887888531841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17731326672702517184709121 13298495004526887888531841)
      ·
        refine ⟨9973871253395165916398881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13298495004526887888531841 9973871253395165916398881)
        ·
          refine ⟨7480403440046374437299161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9973871253395165916398881 7480403440046374437299161)
          ·
            refine ⟨5610302580034780827974371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7480403440046374437299161 5610302580034780827974371)
            ·
              refine ⟨8415453870052171241961557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5610302580034780827974371 8415453870052171241961557)
              ·
                refine ⟨98618600039673881741737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8415453870052171241961557 98618600039673881741737)
                ·
                  rfl

theorem cell22_2592797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 8].length) (baseStart_2592797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2592797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2592797 prefixEnd_2592797 := by exact prefixLift 2592797
  have htrace : WordTrace (prefixWord ++ tailWord_2592797) baseStart_2592797 baseEnd_2592797 := by
    simpa [prefixWord, tailWord_2592797, baseEnd_2592797] using wordTrace_append hprefix tailTrace_2592797
  have hstable : (prefixWord ++ tailWord_2592797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592797).length < 2 ^ (prefixWord ++ tailWord_2592797).sum := by decide
  have hdescent : baseEnd_2592797 < baseStart_2592797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592904 : List Nat := [2, 1, 3, 4, 1, 2, 1, 2, 6]
def baseStart_2592904 : Nat := 118140960795 + 2592904 * 2 ^ 59
def prefixEnd_2592904 : Nat := 4983230072969 + 3 ^ 40 * 2592904 * 2
def baseEnd_2592904 : Nat := 295868009547917441083435

theorem tailTrace_2592904 : CollatzResearch.WordTrace tailWord_2592904 prefixEnd_2592904 295868009547917441083435 := by
  unfold tailWord_2592904
  simp only [CollatzResearch.WordTrace]
  refine ⟨47285489099179557796296883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63047318798906077061729177 47285489099179557796296883)
  ·
    refine ⟨70928233648769336694445325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47285489099179557796296883 70928233648769336694445325)
    ·
      refine ⟨26598087618288501260416997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70928233648769336694445325 26598087618288501260416997)
      ·
        refine ⟨4987141428429093986328187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26598087618288501260416997 4987141428429093986328187)
        ·
          refine ⟨7480712142643640979492281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4987141428429093986328187 7480712142643640979492281)
          ·
            refine ⟨5610534106982730734619211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7480712142643640979492281 5610534106982730734619211)
            ·
              refine ⟨8415801160474096101928817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5610534106982730734619211 8415801160474096101928817)
              ·
                refine ⟨6311850870355572076446613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8415801160474096101928817 6311850870355572076446613)
                ·
                  refine ⟨295868009547917441083435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6311850870355572076446613 295868009547917441083435)
                  ·
                    rfl

theorem cell22_2592904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 6].length) (baseStart_2592904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2592904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2592904 prefixEnd_2592904 := by exact prefixLift 2592904
  have htrace : WordTrace (prefixWord ++ tailWord_2592904) baseStart_2592904 baseEnd_2592904 := by
    simpa [prefixWord, tailWord_2592904, baseEnd_2592904] using wordTrace_append hprefix tailTrace_2592904
  have hstable : (prefixWord ++ tailWord_2592904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592904).length < 2 ^ (prefixWord ++ tailWord_2592904).sum := by decide
  have hdescent : baseEnd_2592904 < baseStart_2592904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592917 : List Nat := [1, 3, 2, 1, 1, 1, 5, 1, 1, 6]
def baseStart_2592917 : Nat := 118140960795 + 2592917 * 2 ^ 59
def prefixEnd_2592917 : Nat := 4983230072969 + 3 ^ 40 * 2592917 * 2
def baseEnd_2592917 : Nat := 887608478809424622675265

theorem tailTrace_2592917 : CollatzResearch.WordTrace tailWord_2592917 prefixEnd_2592917 887608478809424622675265 := by
  unfold tailWord_2592917
  simp only [CollatzResearch.WordTrace]
  refine ⟨94571452347312018812817005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63047634898208012541878003 94571452347312018812817005)
  ·
    refine ⟨35464294630242007054806377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94571452347312018812817005 35464294630242007054806377)
    ·
      refine ⟨26598220972681505291104783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35464294630242007054806377 26598220972681505291104783)
      ·
        refine ⟨39897331459022257936657175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26598220972681505291104783 39897331459022257936657175)
        ·
          refine ⟨59845997188533386904985763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39897331459022257936657175 59845997188533386904985763)
          ·
            refine ⟨89768995782800080357478645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59845997188533386904985763 89768995782800080357478645)
            ·
              refine ⟨8415843354637507533513623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89768995782800080357478645 8415843354637507533513623)
              ·
                refine ⟨12623765031956261300270435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8415843354637507533513623 12623765031956261300270435)
                ·
                  refine ⟨18935647547934391950405653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12623765031956261300270435 18935647547934391950405653)
                  ·
                    refine ⟨887608478809424622675265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18935647547934391950405653 887608478809424622675265)
                    ·
                      rfl

theorem cell22_2592917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_2592917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2592917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2592917 prefixEnd_2592917 := by exact prefixLift 2592917
  have htrace : WordTrace (prefixWord ++ tailWord_2592917) baseStart_2592917 baseEnd_2592917 := by
    simpa [prefixWord, tailWord_2592917, baseEnd_2592917] using wordTrace_append hprefix tailTrace_2592917
  have hstable : (prefixWord ++ tailWord_2592917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592917).length < 2 ^ (prefixWord ++ tailWord_2592917).sum := by decide
  have hdescent : baseEnd_2592917 < baseStart_2592917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592977 : List Nat := [1, 2, 2, 1, 2, 2, 3, 2, 7]
def baseStart_2592977 : Nat := 118140960795 + 2592977 * 2 ^ 59
def prefixEnd_2592977 : Nat := 4983230072969 + 3 ^ 40 * 2592977 * 2
def baseEnd_2592977 : Nat := 295876339345201488725027

theorem tailTrace_2592977 : CollatzResearch.WordTrace tailWord_2592977 prefixEnd_2592977 295876339345201488725027 := by
  unfold tailWord_2592977
  simp only [CollatzResearch.WordTrace]
  refine ⟨94573640727094649060001185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63049093818063099373334123 94573640727094649060001185)
  ·
    refine ⟨70930230545320986795000889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94573640727094649060001185 70930230545320986795000889)
    ·
      refine ⟨53197672908990740096250667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70930230545320986795000889 53197672908990740096250667)
      ·
        refine ⟨79796509363486110144376001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53197672908990740096250667 79796509363486110144376001)
        ·
          refine ⟨59847382022614582608282001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79796509363486110144376001 59847382022614582608282001)
          ·
            refine ⟨44885536516960936956211501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59847382022614582608282001 44885536516960936956211501)
            ·
              refine ⟨16832076193860351358579313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44885536516960936956211501 16832076193860351358579313)
              ·
                refine ⟨12624057145395263518934485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16832076193860351358579313 12624057145395263518934485)
                ·
                  refine ⟨295876339345201488725027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12624057145395263518934485 295876339345201488725027)
                  ·
                    rfl

theorem cell22_2592977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 7].length) (baseStart_2592977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2592977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2592977 prefixEnd_2592977 := by exact prefixLift 2592977
  have htrace : WordTrace (prefixWord ++ tailWord_2592977) baseStart_2592977 baseEnd_2592977 := by
    simpa [prefixWord, tailWord_2592977, baseEnd_2592977] using wordTrace_append hprefix tailTrace_2592977
  have hstable : (prefixWord ++ tailWord_2592977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592977).length < 2 ^ (prefixWord ++ tailWord_2592977).sum := by decide
  have hdescent : baseEnd_2592977 < baseStart_2592977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593071 : List Nat := [1, 1, 2, 1, 2, 1, 6, 3, 2, 3]
def baseStart_2593071 : Nat := 118140960795 + 2593071 * 2 ^ 59
def prefixEnd_2593071 : Nat := 4983230072969 + 3 ^ 40 * 2593071 * 2
def baseEnd_2593071 : Nat := 887661196156619554324793

theorem tailTrace_2593071 : CollatzResearch.WordTrace tailWord_2593071 prefixEnd_2593071 887661196156619554324793 := by
  unfold tailWord_2593071
  simp only [CollatzResearch.WordTrace]
  refine ⟨94577069188754103113923067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63051379459169402075948711 94577069188754103113923067)
  ·
    refine ⟨141865603783131154670884601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94577069188754103113923067 141865603783131154670884601)
    ·
      refine ⟨106399202837348366003163451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141865603783131154670884601 106399202837348366003163451)
      ·
        refine ⟨159598804256022549004745177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106399202837348366003163451 159598804256022549004745177)
        ·
          refine ⟨119699103192016911753558883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159598804256022549004745177 119699103192016911753558883)
          ·
            refine ⟨179548654788025367630338325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119699103192016911753558883 179548654788025367630338325)
            ·
              refine ⟨8416343193188689107672109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 179548654788025367630338325 8416343193188689107672109)
              ·
                refine ⟨3156128697445758415377041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8416343193188689107672109 3156128697445758415377041)
                ·
                  refine ⟨2367096523084318811532781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3156128697445758415377041 2367096523084318811532781)
                  ·
                    refine ⟨887661196156619554324793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2367096523084318811532781 887661196156619554324793)
                    ·
                      rfl

theorem cell22_2593071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 3, 2, 3].length) (baseStart_2593071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2593071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2593071 prefixEnd_2593071 := by exact prefixLift 2593071
  have htrace : WordTrace (prefixWord ++ tailWord_2593071) baseStart_2593071 baseEnd_2593071 := by
    simpa [prefixWord, tailWord_2593071, baseEnd_2593071] using wordTrace_append hprefix tailTrace_2593071
  have hstable : (prefixWord ++ tailWord_2593071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593071).length < 2 ^ (prefixWord ++ tailWord_2593071).sum := by decide
  have hdescent : baseEnd_2593071 < baseStart_2593071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593086 : List Nat := [4, 2, 1, 2, 1, 3, 1, 1, 1, 6]
def baseStart_2593086 : Nat := 118140960795 + 2593086 * 2 ^ 59
def prefixEnd_2593086 : Nat := 4983230072969 + 3 ^ 40 * 2593086 * 2
def baseEnd_2593086 : Nat := 887666330963164515199747

theorem tailTrace_2593086 : CollatzResearch.WordTrace tailWord_2593086 prefixEnd_2593086 887666330963164515199747 := by
  unfold tailWord_2593086
  simp only [CollatzResearch.WordTrace]
  refine ⟨11822202035462470084464889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63051744189133173783812741 11822202035462470084464889)
  ·
    refine ⟨8866651526596852563348667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11822202035462470084464889 8866651526596852563348667)
    ·
      refine ⟨13299977289895278845023001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8866651526596852563348667 13299977289895278845023001)
      ·
        refine ⟨9974982967421459133767251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13299977289895278845023001 9974982967421459133767251)
        ·
          refine ⟨14962474451132188700650877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9974982967421459133767251 14962474451132188700650877)
          ·
            refine ⟨5610927919174570762744079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14962474451132188700650877 5610927919174570762744079)
            ·
              refine ⟨8416391878761856144116119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5610927919174570762744079 8416391878761856144116119)
              ·
                refine ⟨12624587818142784216174179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8416391878761856144116119 12624587818142784216174179)
                ·
                  refine ⟨18936881727214176324261269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12624587818142784216174179 18936881727214176324261269)
                  ·
                    refine ⟨887666330963164515199747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18936881727214176324261269 887666330963164515199747)
                    ·
                      rfl

theorem cell22_2593086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_2593086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2593086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2593086 prefixEnd_2593086 := by exact prefixLift 2593086
  have htrace : WordTrace (prefixWord ++ tailWord_2593086) baseStart_2593086 baseEnd_2593086 := by
    simpa [prefixWord, tailWord_2593086, baseEnd_2593086] using wordTrace_append hprefix tailTrace_2593086
  have hstable : (prefixWord ++ tailWord_2593086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593086).length < 2 ^ (prefixWord ++ tailWord_2593086).sum := by decide
  have hdescent : baseEnd_2593086 < baseStart_2593086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593092 : List Nat := [2, 3, 4, 1, 2, 2, 2, 1, 1, 4]
def baseStart_2593092 : Nat := 118140960795 + 2593092 * 2 ^ 59
def prefixEnd_2593092 : Nat := 4983230072969 + 3 ^ 40 * 2593092 * 2
def baseEnd_2593092 : Nat := 887668384885782499549729

theorem tailTrace_2593092 : CollatzResearch.WordTrace tailWord_2593092 prefixEnd_2593092 887668384885782499549729 := by
  unfold tailWord_2593092
  simp only [CollatzResearch.WordTrace]
  refine ⟨47288917560839011850218765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63051890081118682466958353 47288917560839011850218765)
  ·
    refine ⟨17733344085314629443832037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47288917560839011850218765 17733344085314629443832037)
    ·
      refine ⟨3325002015996493020718507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17733344085314629443832037 3325002015996493020718507)
      ·
        refine ⟨4987503023994739531077761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3325002015996493020718507 4987503023994739531077761)
        ·
          refine ⟨3740627267996054648308321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4987503023994739531077761 3740627267996054648308321)
          ·
            refine ⟨2805470450997040986231241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3740627267996054648308321 2805470450997040986231241)
            ·
              refine ⟨2104102838247780739673431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2805470450997040986231241 2104102838247780739673431)
              ·
                refine ⟨3156154257371671109510147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2104102838247780739673431 3156154257371671109510147)
                ·
                  refine ⟨4734231386057506664265221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3156154257371671109510147 4734231386057506664265221)
                  ·
                    refine ⟨887668384885782499549729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4734231386057506664265221 887668384885782499549729)
                    ·
                      rfl

theorem cell22_2593092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_2593092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2593092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2593092 prefixEnd_2593092 := by exact prefixLift 2593092
  have htrace : WordTrace (prefixWord ++ tailWord_2593092) baseStart_2593092 baseEnd_2593092 := by
    simpa [prefixWord, tailWord_2593092, baseEnd_2593092] using wordTrace_append hprefix tailTrace_2593092
  have hstable : (prefixWord ++ tailWord_2593092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593092).length < 2 ^ (prefixWord ++ tailWord_2593092).sum := by decide
  have hdescent : baseEnd_2593092 < baseStart_2593092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593223 : List Nat := [1, 1, 4, 1, 1, 4, 1, 4, 2, 3]
def baseStart_2593223 : Nat := 118140960795 + 2593223 * 2 ^ 59
def prefixEnd_2593223 : Nat := 4983230072969 + 3 ^ 40 * 2593223 * 2
def baseEnd_2593223 : Nat := 887713228862941824524327

theorem tailTrace_2593223 : CollatzResearch.WordTrace tailWord_2593223 prefixEnd_2593223 887713228862941824524327 := by
  unfold tailWord_2593223
  simp only [CollatzResearch.WordTrace]
  refine ⟨94582613084203433073456323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63055075389468955382304215 94582613084203433073456323)
  ·
    refine ⟨141873919626305149610184485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94582613084203433073456323 141873919626305149610184485)
    ·
      refine ⟨26601359929932215551909591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141873919626305149610184485 26601359929932215551909591)
      ·
        refine ⟨39902039894898323327864387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26601359929932215551909591 39902039894898323327864387)
        ·
          refine ⟨59853059842347484991796581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39902039894898323327864387 59853059842347484991796581)
          ·
            refine ⟨11222448720440153435961859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59853059842347484991796581 11222448720440153435961859)
            ·
              refine ⟨16833673080660230153942789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11222448720440153435961859 16833673080660230153942789)
              ·
                refine ⟨3156313702623793153864273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16833673080660230153942789 3156313702623793153864273)
                ·
                  refine ⟨2367235276967844865398205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3156313702623793153864273 2367235276967844865398205)
                  ·
                    refine ⟨887713228862941824524327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2367235276967844865398205 887713228862941824524327)
                    ·
                      rfl

theorem cell22_2593223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 4, 2, 3].length) (baseStart_2593223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2593223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2593223 prefixEnd_2593223 := by exact prefixLift 2593223
  have htrace : WordTrace (prefixWord ++ tailWord_2593223) baseStart_2593223 baseEnd_2593223 := by
    simpa [prefixWord, tailWord_2593223, baseEnd_2593223] using wordTrace_append hprefix tailTrace_2593223
  have hstable : (prefixWord ++ tailWord_2593223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593223).length < 2 ^ (prefixWord ++ tailWord_2593223).sum := by decide
  have hdescent : baseEnd_2593223 < baseStart_2593223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593238 : List Nat := [5, 2, 1, 1, 1, 1, 2, 2, 1, 6]
def baseStart_2593238 : Nat := 118140960795 + 2593238 * 2 ^ 59
def prefixEnd_2593238 : Nat := 4983230072969 + 3 ^ 40 * 2593238 * 2
def baseEnd_2593238 : Nat := 887718363669486785399281

theorem tailTrace_2593238 : CollatzResearch.WordTrace tailWord_2593238 prefixEnd_2593238 887718363669486785399281 := by
  unfold tailWord_2593238
  simp only [CollatzResearch.WordTrace]
  refine ⟨5911447511196818164703273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63055440119432727090168245 5911447511196818164703273)
  ·
    refine ⟨4433585633397613623527455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5911447511196818164703273 4433585633397613623527455)
    ·
      refine ⟨6650378450096420435291183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4433585633397613623527455 6650378450096420435291183)
      ·
        refine ⟨9975567675144630652936775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6650378450096420435291183 9975567675144630652936775)
        ·
          refine ⟨14963351512716945979405163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9975567675144630652936775 14963351512716945979405163)
          ·
            refine ⟨22445027269075418969107745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14963351512716945979405163 22445027269075418969107745)
            ·
              refine ⟨16833770451806564226830809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22445027269075418969107745 16833770451806564226830809)
              ·
                refine ⟨12625327838854923170123107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16833770451806564226830809 12625327838854923170123107)
                ·
                  refine ⟨18937991758282384755184661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12625327838854923170123107 18937991758282384755184661)
                  ·
                    refine ⟨887718363669486785399281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18937991758282384755184661 887718363669486785399281)
                    ·
                      rfl

theorem cell22_2593238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_2593238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2593238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2593238 prefixEnd_2593238 := by exact prefixLift 2593238
  have htrace : WordTrace (prefixWord ++ tailWord_2593238) baseStart_2593238 baseEnd_2593238 := by
    simpa [prefixWord, tailWord_2593238, baseEnd_2593238] using wordTrace_append hprefix tailTrace_2593238
  have hstable : (prefixWord ++ tailWord_2593238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593238).length < 2 ^ (prefixWord ++ tailWord_2593238).sum := by decide
  have hdescent : baseEnd_2593238 < baseStart_2593238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593285 : List Nat := [1, 3, 1, 1, 2, 2, 4, 4, 1, 3]
def baseStart_2593285 : Nat := 118140960795 + 2593285 * 2 ^ 59
def prefixEnd_2593285 : Nat := 4983230072969 + 3 ^ 40 * 2593285 * 2
def baseEnd_2593285 : Nat := 887734452729994329474137

theorem tailTrace_2593285 : CollatzResearch.WordTrace tailWord_2593285 prefixEnd_2593285 887734452729994329474137 := by
  unfold tailWord_2593285
  simp only [CollatzResearch.WordTrace]
  refine ⟨94584874409978817662213309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63056582939985878441475539 94584874409978817662213309)
  ·
    refine ⟨35469327903742056623329991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94584874409978817662213309 35469327903742056623329991)
    ·
      refine ⟨53203991855613084934994987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35469327903742056623329991 53203991855613084934994987)
      ·
        refine ⟨79805987783419627402492481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53203991855613084934994987 79805987783419627402492481)
        ·
          refine ⟨59854490837564720551869361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79805987783419627402492481 59854490837564720551869361)
          ·
            refine ⟨44890868128173540413902021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59854490837564720551869361 44890868128173540413902021)
            ·
              refine ⟨8417037774032538827606629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44890868128173540413902021 8417037774032538827606629)
              ·
                refine ⟨1578194582631101030176243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8417037774032538827606629 1578194582631101030176243)
                ·
                  refine ⟨2367291873946651545264365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1578194582631101030176243 2367291873946651545264365)
                  ·
                    refine ⟨887734452729994329474137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2367291873946651545264365 887734452729994329474137)
                    ·
                      rfl

theorem cell22_2593285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 4, 1, 3].length) (baseStart_2593285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2593285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2593285 prefixEnd_2593285 := by exact prefixLift 2593285
  have htrace : WordTrace (prefixWord ++ tailWord_2593285) baseStart_2593285 baseEnd_2593285 := by
    simpa [prefixWord, tailWord_2593285, baseEnd_2593285] using wordTrace_append hprefix tailTrace_2593285
  have hstable : (prefixWord ++ tailWord_2593285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593285).length < 2 ^ (prefixWord ++ tailWord_2593285).sum := by decide
  have hdescent : baseEnd_2593285 < baseStart_2593285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593328 : List Nat := [2, 1, 1, 1, 2, 3, 4, 3, 1, 4]
def baseStart_2593328 : Nat := 118140960795 + 2593328 * 2 ^ 59
def prefixEnd_2593328 : Nat := 4983230072969 + 3 ^ 40 * 2593328 * 2
def baseEnd_2593328 : Nat := 887749172508756550649005

theorem tailTrace_2593328 : CollatzResearch.WordTrace tailWord_2593328 prefixEnd_2593328 887749172508756550649005 := by
  unfold tailWord_2593328
  simp only [CollatzResearch.WordTrace]
  refine ⟨47293221374411518003014319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63057628499215357337352425 47293221374411518003014319)
  ·
    refine ⟨70939832061617277004521479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47293221374411518003014319 70939832061617277004521479)
    ·
      refine ⟨106409748092425915506782219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70939832061617277004521479 106409748092425915506782219)
      ·
        refine ⟨159614622138638873260173329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106409748092425915506782219 159614622138638873260173329)
        ·
          refine ⟨119710966603979154945129997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159614622138638873260173329 119710966603979154945129997)
          ·
            refine ⟨44891612476492183104423749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119710966603979154945129997 44891612476492183104423749)
            ·
              refine ⟨8417177339342284332079453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44891612476492183104423749 8417177339342284332079453)
              ·
                refine ⟨3156441502253356624529795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8417177339342284332079453 3156441502253356624529795)
                ·
                  refine ⟨4734662253380034936794693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3156441502253356624529795 4734662253380034936794693)
                  ·
                    refine ⟨887749172508756550649005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4734662253380034936794693 887749172508756550649005)
                    ·
                      rfl

theorem cell22_2593328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 3, 1, 4].length) (baseStart_2593328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2593328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2593328 prefixEnd_2593328 := by exact prefixLift 2593328
  have htrace : WordTrace (prefixWord ++ tailWord_2593328) baseStart_2593328 baseEnd_2593328 := by
    simpa [prefixWord, tailWord_2593328, baseEnd_2593328] using wordTrace_append hprefix tailTrace_2593328
  have hstable : (prefixWord ++ tailWord_2593328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593328).length < 2 ^ (prefixWord ++ tailWord_2593328).sum := by decide
  have hdescent : baseEnd_2593328 < baseStart_2593328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593390 : List Nat := [4, 1, 2, 2, 2, 1, 2, 2, 2, 4]
def baseStart_2593390 : Nat := 118140960795 + 2593390 * 2 ^ 59
def prefixEnd_2593390 : Nat := 4983230072969 + 3 ^ 40 * 2593390 * 2
def baseEnd_2593390 : Nat := 887770396375809055598815

theorem tailTrace_2593390 : CollatzResearch.WordTrace tailWord_2593390 prefixEnd_2593390 887770396375809055598815 := by
  unfold tailWord_2593390
  simp only [CollatzResearch.WordTrace]
  refine ⟨11823588009324802574348203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63059136049732280396523749 11823588009324802574348203)
  ·
    refine ⟨17735382013987203861522305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11823588009324802574348203 17735382013987203861522305)
    ·
      refine ⟨13301536510490402896141729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17735382013987203861522305 13301536510490402896141729)
      ·
        refine ⟨9976152382867802172106297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13301536510490402896141729 9976152382867802172106297)
        ·
          refine ⟨7482114287150851629079723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9976152382867802172106297 7482114287150851629079723)
          ·
            refine ⟨11223171430726277443619585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7482114287150851629079723 11223171430726277443619585)
            ·
              refine ⟨8417378573044708082714689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11223171430726277443619585 8417378573044708082714689)
              ·
                refine ⟨6313033929783531062036017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8417378573044708082714689 6313033929783531062036017)
                ·
                  refine ⟨4734775447337648296527013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6313033929783531062036017 4734775447337648296527013)
                  ·
                    refine ⟨887770396375809055598815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4734775447337648296527013 887770396375809055598815)
                    ·
                      rfl

theorem cell22_2593390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_2593390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2593390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2593390 prefixEnd_2593390 := by exact prefixLift 2593390
  have htrace : WordTrace (prefixWord ++ tailWord_2593390) baseStart_2593390 baseEnd_2593390 := by
    simpa [prefixWord, tailWord_2593390, baseEnd_2593390] using wordTrace_append hprefix tailTrace_2593390
  have hstable : (prefixWord ++ tailWord_2593390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593390).length < 2 ^ (prefixWord ++ tailWord_2593390).sum := by decide
  have hdescent : baseEnd_2593390 < baseStart_2593390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593392 : List Nat := [2, 1, 1, 1, 7, 1, 2, 2, 2, 3]
def baseStart_2593392 : Nat := 118140960795 + 2593392 * 2 ^ 59
def prefixEnd_2593392 : Nat := 4983230072969 + 3 ^ 40 * 2593392 * 2
def baseEnd_2593392 : Nat := 887771081016681717048809

theorem tailTrace_2593392 : CollatzResearch.WordTrace tailWord_2593392 prefixEnd_2593392 887771081016681717048809 := by
  unfold tailWord_2593392
  simp only [CollatzResearch.WordTrace]
  refine ⟨47294388510295587468179215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63059184680394116624238953 47294388510295587468179215)
  ·
    refine ⟨70941582765443381202268823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47294388510295587468179215 70941582765443381202268823)
    ·
      refine ⟨106412374148165071803403235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70941582765443381202268823 106412374148165071803403235)
      ·
        refine ⟨159618561222247607705104853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106412374148165071803403235 159618561222247607705104853)
        ·
          refine ⟨3741060028646428305588395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 159618561222247607705104853 3741060028646428305588395)
          ·
            refine ⟨5611590042969642458382593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3741060028646428305588395 5611590042969642458382593)
            ·
              refine ⟨4208692532227231843786945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5611590042969642458382593 4208692532227231843786945)
              ·
                refine ⟨3156519399170423882840209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4208692532227231843786945 3156519399170423882840209)
                ·
                  refine ⟨2367389549377817912130157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3156519399170423882840209 2367389549377817912130157)
                  ·
                    refine ⟨887771081016681717048809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2367389549377817912130157 887771081016681717048809)
                    ·
                      rfl

theorem cell22_2593392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 2, 2, 3].length) (baseStart_2593392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2593392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2593392 prefixEnd_2593392 := by exact prefixLift 2593392
  have htrace : WordTrace (prefixWord ++ tailWord_2593392) baseStart_2593392 baseEnd_2593392 := by
    simpa [prefixWord, tailWord_2593392, baseEnd_2593392] using wordTrace_append hprefix tailTrace_2593392
  have hstable : (prefixWord ++ tailWord_2593392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593392).length < 2 ^ (prefixWord ++ tailWord_2593392).sum := by decide
  have hdescent : baseEnd_2593392 < baseStart_2593392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593394 : List Nat := [3, 2, 1, 2, 4, 2, 2, 2, 4]
def baseStart_2593394 : Nat := 118140960795 + 2593394 * 2 ^ 59
def prefixEnd_2593394 : Nat := 4983230072969 + 3 ^ 40 * 2593394 * 2
def baseEnd_2593394 : Nat := 295923921885851459499601

theorem tailTrace_2593394 : CollatzResearch.WordTrace tailWord_2593394 prefixEnd_2593394 295923921885851459499601 := by
  unfold tailWord_2593394
  simp only [CollatzResearch.WordTrace]
  refine ⟨23647212491645982319482809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63059233311055952851954157 23647212491645982319482809)
  ·
    refine ⟨17735409368734486739612107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23647212491645982319482809 17735409368734486739612107)
    ·
      refine ⟨26603114053101730109418161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17735409368734486739612107 26603114053101730109418161)
      ·
        refine ⟨19952335539826297582063621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26603114053101730109418161 19952335539826297582063621)
        ·
          refine ⟨3741062913717430796636929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19952335539826297582063621 3741062913717430796636929)
          ·
            refine ⟨2805797185288073097477697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3741062913717430796636929 2805797185288073097477697)
            ·
              refine ⟨2104347888966054823108273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2805797185288073097477697 2104347888966054823108273)
              ·
                refine ⟨1578260916724541117331205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2104347888966054823108273 1578260916724541117331205)
                ·
                  refine ⟨295923921885851459499601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1578260916724541117331205 295923921885851459499601)
                  ·
                    rfl

theorem cell22_2593394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 2, 4].length) (baseStart_2593394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2593394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2593394 prefixEnd_2593394 := by exact prefixLift 2593394
  have htrace : WordTrace (prefixWord ++ tailWord_2593394) baseStart_2593394 baseEnd_2593394 := by
    simpa [prefixWord, tailWord_2593394, baseEnd_2593394] using wordTrace_append hprefix tailTrace_2593394
  have hstable : (prefixWord ++ tailWord_2593394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593394).length < 2 ^ (prefixWord ++ tailWord_2593394).sum := by decide
  have hdescent : baseEnd_2593394 < baseStart_2593394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593405 : List Nat := [1, 4, 1, 1, 5, 2, 1, 7]
def baseStart_2593405 : Nat := 118140960795 + 2593405 * 2 ^ 59
def prefixEnd_2593405 : Nat := 4983230072969 + 3 ^ 40 * 2593405 * 2
def baseEnd_2593405 : Nat := 98641725686928224052641

theorem tailTrace_2593405 : CollatzResearch.WordTrace tailWord_2593405 prefixEnd_2593405 98641725686928224052641 := by
  unfold tailWord_2593405
  simp only [CollatzResearch.WordTrace]
  refine ⟨94589251169544078156581669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63059500779696052104387779 94589251169544078156581669)
  ·
    refine ⟨17735484594289514654359063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94589251169544078156581669 17735484594289514654359063)
    ·
      refine ⟨26603226891434271981538595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17735484594289514654359063 26603226891434271981538595)
      ·
        refine ⟨39904840337151407972307893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26603226891434271981538595 39904840337151407972307893)
        ·
          refine ⟨3741078781607944497403865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39904840337151407972307893 3741078781607944497403865)
          ·
            refine ⟨2805809086205958373052899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3741078781607944497403865 2805809086205958373052899)
            ·
              refine ⟨4208713629308937559579349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2805809086205958373052899 4208713629308937559579349)
              ·
                refine ⟨98641725686928224052641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4208713629308937559579349 98641725686928224052641)
                ·
                  rfl

theorem cell22_2593405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 7].length) (baseStart_2593405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2593405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2593405 prefixEnd_2593405 := by exact prefixLift 2593405
  have htrace : WordTrace (prefixWord ++ tailWord_2593405) baseStart_2593405 baseEnd_2593405 := by
    simpa [prefixWord, tailWord_2593405, baseEnd_2593405] using wordTrace_append hprefix tailTrace_2593405
  have hstable : (prefixWord ++ tailWord_2593405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593405).length < 2 ^ (prefixWord ++ tailWord_2593405).sum := by decide
  have hdescent : baseEnd_2593405 < baseStart_2593405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593437 : List Nat := [1, 4, 2, 1, 1, 1, 3, 5, 1, 3]
def baseStart_2593437 : Nat := 118140960795 + 2593437 * 2 ^ 59
def prefixEnd_2593437 : Nat := 4983230072969 + 3 ^ 40 * 2593437 * 2
def baseEnd_2593437 : Nat := 887786485436316599673671

theorem tailTrace_2593437 : CollatzResearch.WordTrace tailWord_2593437 prefixEnd_2593437 887786485436316599673671 := by
  unfold tailWord_2593437
  simp only [CollatzResearch.WordTrace]
  refine ⟨94590418305428147621746565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63060278870285431747831043 94590418305428147621746565)
  ·
    refine ⟨17735703432267777679077481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94590418305428147621746565 17735703432267777679077481)
    ·
      refine ⟨13301777574200833259308111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17735703432267777679077481 13301777574200833259308111)
      ·
        refine ⟨19952666361301249888962167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13301777574200833259308111 19952666361301249888962167)
        ·
          refine ⟨29928999541951874833443251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19952666361301249888962167 29928999541951874833443251)
          ·
            refine ⟨44893499312927812250164877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29928999541951874833443251 44893499312927812250164877)
            ·
              refine ⟨16835062242347929593811829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44893499312927812250164877 16835062242347929593811829)
              ·
                refine ⟨1578287085220118399419859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16835062242347929593811829 1578287085220118399419859)
                ·
                  refine ⟨2367430627830177599129789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1578287085220118399419859 2367430627830177599129789)
                  ·
                    refine ⟨887786485436316599673671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2367430627830177599129789 887786485436316599673671)
                    ·
                      rfl

theorem cell22_2593437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_2593437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2593437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2593437 prefixEnd_2593437 := by exact prefixLift 2593437
  have htrace : WordTrace (prefixWord ++ tailWord_2593437) baseStart_2593437 baseEnd_2593437 := by
    simpa [prefixWord, tailWord_2593437, baseEnd_2593437] using wordTrace_append hprefix tailTrace_2593437
  have hstable : (prefixWord ++ tailWord_2593437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593437).length < 2 ^ (prefixWord ++ tailWord_2593437).sum := by decide
  have hdescent : baseEnd_2593437 < baseStart_2593437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593454 : List Nat := [4, 1, 4, 1, 1, 2, 2, 1, 3, 3]
def baseStart_2593454 : Nat := 118140960795 + 2593454 * 2 ^ 59
def prefixEnd_2593454 : Nat := 4983230072969 + 3 ^ 40 * 2593454 * 2
def baseEnd_2593454 : Nat := 887792304883734221998619

theorem tailTrace_2593454 : CollatzResearch.WordTrace tailWord_2593454 prefixEnd_2593454 887792304883734221998619 := by
  unfold tailWord_2593454
  simp only [CollatzResearch.WordTrace]
  refine ⟨11823879793295819940639427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63060692230911039683410277 11823879793295819940639427)
  ·
    refine ⟨17735819689943729910959141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11823879793295819940639427 17735819689943729910959141)
    ·
      refine ⟨3325466191864449358304839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17735819689943729910959141 3325466191864449358304839)
      ·
        refine ⟨4988199287796674037457259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3325466191864449358304839 4988199287796674037457259)
        ·
          refine ⟨7482298931695011056185889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4988199287796674037457259 7482298931695011056185889)
          ·
            refine ⟨5611724198771258292139417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7482298931695011056185889 5611724198771258292139417)
            ·
              refine ⟨4208793149078443719104563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5611724198771258292139417 4208793149078443719104563)
              ·
                refine ⟨6313189723617665578656845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4208793149078443719104563 6313189723617665578656845)
                ·
                  refine ⟨2367446146356624591996317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6313189723617665578656845 2367446146356624591996317)
                  ·
                    refine ⟨887792304883734221998619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2367446146356624591996317 887792304883734221998619)
                    ·
                      rfl

theorem cell22_2593454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_2593454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2593454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2593454 prefixEnd_2593454 := by exact prefixLift 2593454
  have htrace : WordTrace (prefixWord ++ tailWord_2593454) baseStart_2593454 baseEnd_2593454 := by
    simpa [prefixWord, tailWord_2593454, baseEnd_2593454] using wordTrace_append hprefix tailTrace_2593454
  have hstable : (prefixWord ++ tailWord_2593454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593454).length < 2 ^ (prefixWord ++ tailWord_2593454).sum := by decide
  have hdescent : baseEnd_2593454 < baseStart_2593454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593480 : List Nat := [2, 1, 3, 1, 2, 3, 1, 4, 1, 4]
def baseStart_2593480 : Nat := 118140960795 + 2593480 * 2 ^ 59
def prefixEnd_2593480 : Nat := 4983230072969 + 3 ^ 40 * 2593480 * 2
def baseEnd_2593480 : Nat := 887801205215078820848539

theorem tailTrace_2593480 : CollatzResearch.WordTrace tailWord_2593480 prefixEnd_2593480 887801205215078820848539 := by
  unfold tailWord_2593480
  simp only [CollatzResearch.WordTrace]
  refine ⟨47295993322136182982780947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63061324429514910643707929 47295993322136182982780947)
  ·
    refine ⟨70943989983204274474171421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47295993322136182982780947 70943989983204274474171421)
    ·
      refine ⟨26603996243701602927814283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70943989983204274474171421 26603996243701602927814283)
      ·
        refine ⟨39905994365552404391721425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26603996243701602927814283 39905994365552404391721425)
        ·
          refine ⟨29929495774164303293791069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39905994365552404391721425 29929495774164303293791069)
          ·
            refine ⟨11223560915311613735171651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29929495774164303293791069 11223560915311613735171651)
            ·
              refine ⟨16835341372967420602757477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11223560915311613735171651 16835341372967420602757477)
              ·
                refine ⟨3156626507431391363017027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16835341372967420602757477 3156626507431391363017027)
                ·
                  refine ⟨4734939761147087044525541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3156626507431391363017027 4734939761147087044525541)
                  ·
                    refine ⟨887801205215078820848539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4734939761147087044525541 887801205215078820848539)
                    ·
                      rfl

theorem cell22_2593480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_2593480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2593480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2593480 prefixEnd_2593480 := by exact prefixLift 2593480
  have htrace : WordTrace (prefixWord ++ tailWord_2593480) baseStart_2593480 baseEnd_2593480 := by
    simpa [prefixWord, tailWord_2593480, baseEnd_2593480] using wordTrace_append hprefix tailTrace_2593480
  have hstable : (prefixWord ++ tailWord_2593480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593480).length < 2 ^ (prefixWord ++ tailWord_2593480).sum := by decide
  have hdescent : baseEnd_2593480 < baseStart_2593480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593512 : List Nat := [2, 1, 4, 1, 4, 2, 1, 1, 6]
def baseStart_2593512 : Nat := 118140960795 + 2593512 * 2 ^ 59
def prefixEnd_2593512 : Nat := 4983230072969 + 3 ^ 40 * 2593512 * 2
def baseEnd_2593512 : Nat := 295937386489680468016147

theorem tailTrace_2593512 : CollatzResearch.WordTrace tailWord_2593512 prefixEnd_2593512 295937386489680468016147 := by
  unfold tailWord_2593512
  simp only [CollatzResearch.WordTrace]
  refine ⟨47296576890078217715363395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63062102520104290287151193 47296576890078217715363395)
  ·
    refine ⟨70944865335117326573045093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47296576890078217715363395 70944865335117326573045093)
    ·
      refine ⟨13302162250334498732445955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70944865335117326573045093 13302162250334498732445955)
      ·
        refine ⟨19953243375501748098668933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13302162250334498732445955 19953243375501748098668933)
        ·
          refine ⟨3741233132906577768500425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19953243375501748098668933 3741233132906577768500425)
          ·
            refine ⟨2805924849679933326375319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3741233132906577768500425 2805924849679933326375319)
            ·
              refine ⟨4208887274519899989562979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2805924849679933326375319 4208887274519899989562979)
              ·
                refine ⟨6313330911779849984344469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4208887274519899989562979 6313330911779849984344469)
                ·
                  refine ⟨295937386489680468016147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6313330911779849984344469 295937386489680468016147)
                  ·
                    rfl

theorem cell22_2593512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 6].length) (baseStart_2593512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2593512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2593512 prefixEnd_2593512 := by exact prefixLift 2593512
  have htrace : WordTrace (prefixWord ++ tailWord_2593512) baseStart_2593512 baseEnd_2593512 := by
    simpa [prefixWord, tailWord_2593512, baseEnd_2593512] using wordTrace_append hprefix tailTrace_2593512
  have hstable : (prefixWord ++ tailWord_2593512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593512).length < 2 ^ (prefixWord ++ tailWord_2593512).sum := by decide
  have hdescent : baseEnd_2593512 < baseStart_2593512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593570 : List Nat := [3, 3, 1, 1, 2, 2, 1, 1, 2, 6]
def baseStart_2593570 : Nat := 118140960795 + 2593570 * 2 ^ 59
def prefixEnd_2593570 : Nat := 4983230072969 + 3 ^ 40 * 2593570 * 2
def baseEnd_2593570 : Nat := 887832014054348586098263

theorem tailTrace_2593570 : CollatzResearch.WordTrace tailWord_2593570 prefixEnd_2593570 887832014054348586098263 := by
  unfold tailWord_2593570
  simp only [CollatzResearch.WordTrace]
  refine ⟨23648817303486577834084541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63063512809297540890892109 23648817303486577834084541)
  ·
    refine ⟨8868306488807466687781703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23648817303486577834084541 8868306488807466687781703)
    ·
      refine ⟨13302459733211200031672555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8868306488807466687781703 13302459733211200031672555)
      ·
        refine ⟨19953689599816800047508833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13302459733211200031672555 19953689599816800047508833)
        ·
          refine ⟨14965267199862600035631625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19953689599816800047508833 14965267199862600035631625)
          ·
            refine ⟨11223950399896950026723719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14965267199862600035631625 11223950399896950026723719)
            ·
              refine ⟨16835925599845425040085579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11223950399896950026723719 16835925599845425040085579)
              ·
                refine ⟨25253888399768137560128369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16835925599845425040085579 25253888399768137560128369)
                ·
                  refine ⟨18940416299826103170096277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25253888399768137560128369 18940416299826103170096277)
                  ·
                    refine ⟨887832014054348586098263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18940416299826103170096277 887832014054348586098263)
                    ·
                      rfl

theorem cell22_2593570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_2593570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2593570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2593570 prefixEnd_2593570 := by exact prefixLift 2593570
  have htrace : WordTrace (prefixWord ++ tailWord_2593570) baseStart_2593570 baseEnd_2593570 := by
    simpa [prefixWord, tailWord_2593570, baseEnd_2593570] using wordTrace_append hprefix tailTrace_2593570
  have hstable : (prefixWord ++ tailWord_2593570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593570).length < 2 ^ (prefixWord ++ tailWord_2593570).sum := by decide
  have hdescent : baseEnd_2593570 < baseStart_2593570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593585 : List Nat := [1, 2, 2, 3, 2, 1, 1, 5, 5]
def baseStart_2593585 : Nat := 118140960795 + 2593585 * 2 ^ 59
def prefixEnd_2593585 : Nat := 4983230072969 + 3 ^ 40 * 2593585 * 2
def baseEnd_2593585 : Nat := 295945716286964515657739

theorem tailTrace_2593585 : CollatzResearch.WordTrace tailWord_2593585 prefixEnd_2593585 295945716286964515657739 := by
  unfold tailWord_2593585
  simp only [CollatzResearch.WordTrace]
  refine ⟨94595816308891968898134209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63063877539261312598756139 94595816308891968898134209)
  ·
    refine ⟨70946862231668976673600657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94595816308891968898134209 70946862231668976673600657)
    ·
      refine ⟨53210146673751732505200493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70946862231668976673600657 53210146673751732505200493)
      ·
        refine ⟨19953805002656899689450185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53210146673751732505200493 19953805002656899689450185)
        ·
          refine ⟨14965353751992674767087639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19953805002656899689450185 14965353751992674767087639)
          ·
            refine ⟨22448030627989012150631459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14965353751992674767087639 22448030627989012150631459)
            ·
              refine ⟨33672045941983518225947189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22448030627989012150631459 33672045941983518225947189)
              ·
                refine ⟨3156754307060954833682549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33672045941983518225947189 3156754307060954833682549)
                ·
                  refine ⟨295945716286964515657739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3156754307060954833682549 295945716286964515657739)
                  ·
                    rfl

theorem cell22_2593585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 5, 5].length) (baseStart_2593585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2593585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2593585 prefixEnd_2593585 := by exact prefixLift 2593585
  have htrace : WordTrace (prefixWord ++ tailWord_2593585) baseStart_2593585 baseEnd_2593585 := by
    simpa [prefixWord, tailWord_2593585, baseEnd_2593585] using wordTrace_append hprefix tailTrace_2593585
  have hstable : (prefixWord ++ tailWord_2593585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593585).length < 2 ^ (prefixWord ++ tailWord_2593585).sum := by decide
  have hdescent : baseEnd_2593585 < baseStart_2593585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593660 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 6, 4]
def baseStart_2593660 : Nat := 118140960795 + 2593660 * 2 ^ 59
def prefixEnd_2593660 : Nat := 4983230072969 + 3 ^ 40 * 2593660 * 2
def baseEnd_2593660 : Nat := 887862822893618351347987

theorem tailTrace_2593660 : CollatzResearch.WordTrace tailWord_2593660 prefixEnd_2593660 887862822893618351347987 := by
  unfold tailWord_2593660
  simp only [CollatzResearch.WordTrace]
  refine ⟨47299275891810128353557217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63065701189080171138076289 47299275891810128353557217)
  ·
    refine ⟨35474456918857596265167913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47299275891810128353557217 35474456918857596265167913)
    ·
      refine ⟨26605842689143197198875935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35474456918857596265167913 26605842689143197198875935)
      ·
        refine ⟨39908764033714795798313903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26605842689143197198875935 39908764033714795798313903)
        ·
          refine ⟨59863146050572193697470855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39908764033714795798313903 59863146050572193697470855)
          ·
            refine ⟨89794719075858290546206283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59863146050572193697470855 89794719075858290546206283)
            ·
              refine ⟨134692078613787435819309425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89794719075858290546206283 134692078613787435819309425)
              ·
                refine ⟨101019058960340576864482069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134692078613787435819309425 101019058960340576864482069)
                ·
                  refine ⟨4735268388765964540522597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 101019058960340576864482069 4735268388765964540522597)
                  ·
                    refine ⟨887862822893618351347987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4735268388765964540522597 887862822893618351347987)
                    ·
                      rfl

theorem cell22_2593660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_2593660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2593660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2593660 prefixEnd_2593660 := by exact prefixLift 2593660
  have htrace : WordTrace (prefixWord ++ tailWord_2593660) baseStart_2593660 baseEnd_2593660 := by
    simpa [prefixWord, tailWord_2593660, baseEnd_2593660] using wordTrace_append hprefix tailTrace_2593660
  have hstable : (prefixWord ++ tailWord_2593660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593660).length < 2 ^ (prefixWord ++ tailWord_2593660).sum := by decide
  have hdescent : baseEnd_2593660 < baseStart_2593660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593752 : List Nat := [2, 1, 2, 2, 2, 4, 1, 1, 2, 5]
def baseStart_2593752 : Nat := 118140960795 + 2593752 * 2 ^ 59
def prefixEnd_2593752 : Nat := 4983230072969 + 3 ^ 40 * 2593752 * 2
def baseEnd_2593752 : Nat := 887894316373760778047705

theorem tailTrace_2593752 : CollatzResearch.WordTrace tailWord_2593752 prefixEnd_2593752 887894316373760778047705 := by
  unfold tailWord_2593752
  simp only [CollatzResearch.WordTrace]
  refine ⟨47300953649643478209731755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63067938199524637612975673 47300953649643478209731755)
  ·
    refine ⟨70951430474465217314597633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47300953649643478209731755 70951430474465217314597633)
    ·
      refine ⟨53213572855848912985948225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70951430474465217314597633 53213572855848912985948225)
      ·
        refine ⟨39910179641886684739461169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53213572855848912985948225 39910179641886684739461169)
        ·
          refine ⟨29932634731415013554595877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39910179641886684739461169 29932634731415013554595877)
          ·
            refine ⟨5612369012140315041486727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29932634731415013554595877 5612369012140315041486727)
            ·
              refine ⟨8418553518210472562230091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5612369012140315041486727 8418553518210472562230091)
              ·
                refine ⟨12627830277315708843345137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8418553518210472562230091 12627830277315708843345137)
                ·
                  refine ⟨9470872707986781632508853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12627830277315708843345137 9470872707986781632508853)
                  ·
                    refine ⟨887894316373760778047705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9470872707986781632508853 887894316373760778047705)
                    ·
                      rfl

theorem cell22_2593752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 2, 5].length) (baseStart_2593752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2593752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2593752 prefixEnd_2593752 := by exact prefixLift 2593752
  have htrace : WordTrace (prefixWord ++ tailWord_2593752) baseStart_2593752 baseEnd_2593752 := by
    simpa [prefixWord, tailWord_2593752, baseEnd_2593752] using wordTrace_append hprefix tailTrace_2593752
  have hstable : (prefixWord ++ tailWord_2593752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593752).length < 2 ^ (prefixWord ++ tailWord_2593752).sum := by decide
  have hdescent : baseEnd_2593752 < baseStart_2593752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593799 : List Nat := [1, 1, 4, 3, 1, 1, 1, 6, 4]
def baseStart_2593799 : Nat := 118140960795 + 2593799 * 2 ^ 59
def prefixEnd_2593799 : Nat := 4983230072969 + 3 ^ 40 * 2593799 * 2
def baseEnd_2593799 : Nat := 295970135144756107374187

theorem tailTrace_2593799 : CollatzResearch.WordTrace tailWord_2593799 prefixEnd_2593799 295970135144756107374187 := by
  unfold tailWord_2593799
  simp only [CollatzResearch.WordTrace]
  refine ⟨94603621530116683446424451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63069081020077788964282967 94603621530116683446424451)
  ·
    refine ⟨141905432295175025169636677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94603621530116683446424451 141905432295175025169636677)
    ·
      refine ⟨26607268555345317219306877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141905432295175025169636677 26607268555345317219306877)
      ·
        refine ⟨9977725708254493957240079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26607268555345317219306877 9977725708254493957240079)
        ·
          refine ⟨14966588562381740935860119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9977725708254493957240079 14966588562381740935860119)
          ·
            refine ⟨22449882843572611403790179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14966588562381740935860119 22449882843572611403790179)
            ·
              refine ⟨33674824265358917105685269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22449882843572611403790179 33674824265358917105685269)
              ·
                refine ⟨1578507387438699239328997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33674824265358917105685269 1578507387438699239328997)
                ·
                  refine ⟨295970135144756107374187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1578507387438699239328997 295970135144756107374187)
                  ·
                    rfl

theorem cell22_2593799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 6, 4].length) (baseStart_2593799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2593799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2593799 prefixEnd_2593799 := by exact prefixLift 2593799
  have htrace : WordTrace (prefixWord ++ tailWord_2593799) baseStart_2593799 baseEnd_2593799 := by
    simpa [prefixWord, tailWord_2593799, baseEnd_2593799] using wordTrace_append hprefix tailTrace_2593799
  have hstable : (prefixWord ++ tailWord_2593799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593799).length < 2 ^ (prefixWord ++ tailWord_2593799).sum := by decide
  have hdescent : baseEnd_2593799 < baseStart_2593799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593827 : List Nat := [1, 1, 1, 4, 3, 3, 1, 8]
def baseStart_2593827 : Nat := 118140960795 + 2593827 * 2 ^ 59
def prefixEnd_2593827 : Nat := 4983230072969 + 3 ^ 40 * 2593827 * 2
def baseEnd_2593827 : Nat := 98657776711831731380275

theorem tailTrace_2593827 : CollatzResearch.WordTrace tailWord_2593827 prefixEnd_2593827 98657776711831731380275 := by
  unfold tailWord_2593827
  simp only [CollatzResearch.WordTrace]
  refine ⟨94604642774015244228443735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63069761849343496152295823 94604642774015244228443735)
  ·
    refine ⟨141906964161022866342665603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94604642774015244228443735 141906964161022866342665603)
    ·
      refine ⟨212860446241534299513998405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141906964161022866342665603 212860446241534299513998405)
      ·
        refine ⟨39911333670287681158874701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 212860446241534299513998405 39911333670287681158874701)
        ·
          refine ⟨14966750126357880434578013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39911333670287681158874701 14966750126357880434578013)
          ·
            refine ⟨5612531297384205162966755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14966750126357880434578013 5612531297384205162966755)
            ·
              refine ⟨8418796946076307744450133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5612531297384205162966755 8418796946076307744450133)
              ·
                refine ⟨98657776711831731380275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8418796946076307744450133 98657776711831731380275)
                ·
                  rfl

theorem cell22_2593827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 8].length) (baseStart_2593827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2593827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2593827 prefixEnd_2593827 := by exact prefixLift 2593827
  have htrace : WordTrace (prefixWord ++ tailWord_2593827) baseStart_2593827 baseEnd_2593827 := by
    simpa [prefixWord, tailWord_2593827, baseEnd_2593827] using wordTrace_append hprefix tailTrace_2593827
  have hstable : (prefixWord ++ tailWord_2593827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593827).length < 2 ^ (prefixWord ++ tailWord_2593827).sum := by decide
  have hdescent : baseEnd_2593827 < baseStart_2593827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593831 : List Nat := [1, 1, 7, 1, 1, 1, 1, 2, 4, 3]
def baseStart_2593831 : Nat := 118140960795 + 2593831 * 2 ^ 59
def prefixEnd_2593831 : Nat := 4983230072969 + 3 ^ 40 * 2593831 * 2
def baseEnd_2593831 : Nat := 887921359688230905322463

theorem tailTrace_2593831 : CollatzResearch.WordTrace tailWord_2593831 prefixEnd_2593831 887921359688230905322463 := by
  unfold tailWord_2593831
  simp only [CollatzResearch.WordTrace]
  refine ⟨94604788666000752911589347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63069859110667168607726231 94604788666000752911589347)
  ·
    refine ⟨141907182999001129367384021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94604788666000752911589347 141907182999001129367384021)
    ·
      refine ⟨3325949601539088969548063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 141907182999001129367384021 3325949601539088969548063)
      ·
        refine ⟨4988924402308633454322095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3325949601539088969548063 4988924402308633454322095)
        ·
          refine ⟨7483386603462950181483143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4988924402308633454322095 7483386603462950181483143)
          ·
            refine ⟨11225079905194425272224715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7483386603462950181483143 11225079905194425272224715)
            ·
              refine ⟨16837619857791637908337073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11225079905194425272224715 16837619857791637908337073)
              ·
                refine ⟨12628214893343728431252805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16837619857791637908337073 12628214893343728431252805)
                ·
                  refine ⟨2367790292501949080859901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12628214893343728431252805 2367790292501949080859901)
                  ·
                    refine ⟨887921359688230905322463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2367790292501949080859901 887921359688230905322463)
                    ·
                      rfl

theorem cell22_2593831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_2593831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2593831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2593831 prefixEnd_2593831 := by exact prefixLift 2593831
  have htrace : WordTrace (prefixWord ++ tailWord_2593831) baseStart_2593831 baseEnd_2593831 := by
    simpa [prefixWord, tailWord_2593831, baseEnd_2593831] using wordTrace_append hprefix tailTrace_2593831
  have hstable : (prefixWord ++ tailWord_2593831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593831).length < 2 ^ (prefixWord ++ tailWord_2593831).sum := by decide
  have hdescent : baseEnd_2593831 < baseStart_2593831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593844 : List Nat := [2, 5, 1, 2, 1, 1, 10]
def baseStart_2593844 : Nat := 118140960795 + 2593844 * 2 ^ 59
def prefixEnd_2593844 : Nat := 4983230072969 + 3 ^ 40 * 2593844 * 2
def baseEnd_2593844 : Nat := 32886141105700118694349

theorem tailTrace_2593844 : CollatzResearch.WordTrace tailWord_2593844 prefixEnd_2593844 32886141105700118694349 := by
  unfold tailWord_2593844
  simp only [CollatzResearch.WordTrace]
  refine ⟨47302631407476828065906293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63070175209969104087875057 47302631407476828065906293)
  ·
    refine ⟨4434621694450952631178715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47302631407476828065906293 4434621694450952631178715)
    ·
      refine ⟨6651932541676428946768073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4434621694450952631178715 6651932541676428946768073)
      ·
        refine ⟨4988949406257321710076055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6651932541676428946768073 4988949406257321710076055)
        ·
          refine ⟨7483424109385982565114083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4988949406257321710076055 7483424109385982565114083)
          ·
            refine ⟨11225136164078973847671125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7483424109385982565114083 11225136164078973847671125)
            ·
              refine ⟨32886141105700118694349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11225136164078973847671125 32886141105700118694349)
              ·
                rfl

theorem cell22_2593844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 10].length) (baseStart_2593844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2593844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2593844 prefixEnd_2593844 := by exact prefixLift 2593844
  have htrace : WordTrace (prefixWord ++ tailWord_2593844) baseStart_2593844 baseEnd_2593844 := by
    simpa [prefixWord, tailWord_2593844, baseEnd_2593844] using wordTrace_append hprefix tailTrace_2593844
  have hstable : (prefixWord ++ tailWord_2593844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593844).length < 2 ^ (prefixWord ++ tailWord_2593844).sum := by decide
  have hdescent : baseEnd_2593844 < baseStart_2593844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593846 : List Nat := [5, 1, 2, 1, 1, 3, 1, 2, 2, 4]
def baseStart_2593846 : Nat := 118140960795 + 2593846 * 2 ^ 59
def prefixEnd_2593846 : Nat := 4983230072969 + 3 ^ 40 * 2593846 * 2
def baseEnd_2593846 : Nat := 887926494494775866197417

theorem tailTrace_2593846 : CollatzResearch.WordTrace tailWord_2593846 prefixEnd_2593846 887926494494775866197417 := by
  unfold tailWord_2593846
  simp only [CollatzResearch.WordTrace]
  refine ⟨5912833485059150654586587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63070223840630940315590261 5912833485059150654586587)
  ·
    refine ⟨8869250227588725981879881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5912833485059150654586587 8869250227588725981879881)
    ·
      refine ⟨6651937670691544486409911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8869250227588725981879881 6651937670691544486409911)
      ·
        refine ⟨9977906506037316729614867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6651937670691544486409911 9977906506037316729614867)
        ·
          refine ⟨14966859759055975094422301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9977906506037316729614867 14966859759055975094422301)
          ·
            refine ⟨5612572409645990660408363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14966859759055975094422301 5612572409645990660408363)
            ·
              refine ⟨8418858614468985990612545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5612572409645990660408363 8418858614468985990612545)
              ·
                refine ⟨6314143960851739492959409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8418858614468985990612545 6314143960851739492959409)
                ·
                  refine ⟨4735607970638804619719557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6314143960851739492959409 4735607970638804619719557)
                  ·
                    refine ⟨887926494494775866197417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4735607970638804619719557 887926494494775866197417)
                    ·
                      rfl

theorem cell22_2593846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_2593846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2593846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2593846 prefixEnd_2593846 := by exact prefixLift 2593846
  have htrace : WordTrace (prefixWord ++ tailWord_2593846) baseStart_2593846 baseEnd_2593846 := by
    simpa [prefixWord, tailWord_2593846, baseEnd_2593846] using wordTrace_append hprefix tailTrace_2593846
  have hstable : (prefixWord ++ tailWord_2593846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593846).length < 2 ^ (prefixWord ++ tailWord_2593846).sum := by decide
  have hdescent : baseEnd_2593846 < baseStart_2593846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593934 : List Nat := [4, 1, 1, 3, 2, 1, 1, 1, 8]
def baseStart_2593934 : Nat := 118140960795 + 2593934 * 2 ^ 59
def prefixEnd_2593934 : Nat := 4983230072969 + 3 ^ 40 * 2593934 * 2
def baseEnd_2593934 : Nat := 295985539564390989999049

theorem tailTrace_2593934 : CollatzResearch.WordTrace tailWord_2593934 prefixEnd_2593934 295985539564390989999049 := by
  unfold tailWord_2593934
  simp only [CollatzResearch.WordTrace]
  refine ⟨11826068173078450187823607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63072363589751734335059237 11826068173078450187823607)
  ·
    refine ⟨17739102259617675281735411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11826068173078450187823607 17739102259617675281735411)
    ·
      refine ⟨26608653389426512922603117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17739102259617675281735411 26608653389426512922603117)
      ·
        refine ⟨9978245021034942345976169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26608653389426512922603117 9978245021034942345976169)
        ·
          refine ⟨7483683765776206759482127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9978245021034942345976169 7483683765776206759482127)
          ·
            refine ⟨11225525648664310139223191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7483683765776206759482127 11225525648664310139223191)
            ·
              refine ⟨16838288472996465208834787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11225525648664310139223191 16838288472996465208834787)
              ·
                refine ⟨25257432709494697813252181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16838288472996465208834787 25257432709494697813252181)
                ·
                  refine ⟨295985539564390989999049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25257432709494697813252181 295985539564390989999049)
                  ·
                    rfl

theorem cell22_2593934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_2593934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2593934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2593934 prefixEnd_2593934 := by exact prefixLift 2593934
  have htrace : WordTrace (prefixWord ++ tailWord_2593934) baseStart_2593934 baseEnd_2593934 := by
    simpa [prefixWord, tailWord_2593934, baseEnd_2593934] using wordTrace_append hprefix tailTrace_2593934
  have hstable : (prefixWord ++ tailWord_2593934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593934).length < 2 ^ (prefixWord ++ tailWord_2593934).sum := by decide
  have hdescent : baseEnd_2593934 < baseStart_2593934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593949 : List Nat := [1, 4, 2, 1, 1, 2, 1, 4, 1, 5]
def baseStart_2593949 : Nat := 118140960795 + 2593949 * 2 ^ 59
def prefixEnd_2593949 : Nat := 4983230072969 + 3 ^ 40 * 2593949 * 2
def baseEnd_2593949 : Nat := 887961753499717930872101

theorem tailTrace_2593949 : CollatzResearch.WordTrace tailWord_2593949 prefixEnd_2593949 887961753499717930872101 := by
  unfold tailWord_2593949
  simp only [CollatzResearch.WordTrace]
  refine ⟨94609092479573259064384901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63072728319715506042923267 94609092479573259064384901)
  ·
    refine ⟨17739204839919986074572169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94609092479573259064384901 17739204839919986074572169)
    ·
      refine ⟨13304403629939989555929127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17739204839919986074572169 13304403629939989555929127)
      ·
        refine ⟨19956605444909984333893691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13304403629939989555929127 19956605444909984333893691)
        ·
          refine ⟨29934908167364976500840537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19956605444909984333893691 29934908167364976500840537)
          ·
            refine ⟨22451181125523732375630403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29934908167364976500840537 22451181125523732375630403)
            ·
              refine ⟨33676771688285598563445605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22451181125523732375630403 33676771688285598563445605)
              ·
                refine ⟨6314394691553549730646051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33676771688285598563445605 6314394691553549730646051)
                ·
                  refine ⟨9471592037330324595969077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6314394691553549730646051 9471592037330324595969077)
                  ·
                    refine ⟨887961753499717930872101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9471592037330324595969077 887961753499717930872101)
                    ·
                      rfl

theorem cell22_2593949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_2593949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2593949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2593949 prefixEnd_2593949 := by exact prefixLift 2593949
  have htrace : WordTrace (prefixWord ++ tailWord_2593949) baseStart_2593949 baseEnd_2593949 := by
    simpa [prefixWord, tailWord_2593949, baseEnd_2593949] using wordTrace_append hprefix tailTrace_2593949
  have hstable : (prefixWord ++ tailWord_2593949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593949).length < 2 ^ (prefixWord ++ tailWord_2593949).sum := by decide
  have hdescent : baseEnd_2593949 < baseStart_2593949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594013 : List Nat := [1, 4, 3, 2, 3, 1, 8]
def baseStart_2594013 : Nat := 118140960795 + 2594013 * 2 ^ 59
def prefixEnd_2594013 : Nat := 4983230072969 + 3 ^ 40 * 2594013 * 2
def baseEnd_2594013 : Nat := 32888283778060855454515

theorem tailTrace_2594013 : CollatzResearch.WordTrace tailWord_2594013 prefixEnd_2594013 32888283778060855454515 := by
  unfold tailWord_2594013
  simp only [CollatzResearch.WordTrace]
  refine ⟨94611426751341397994714693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63074284500894265329809795 94611426751341397994714693)
  ·
    refine ⟨17739642515876512124009005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94611426751341397994714693 17739642515876512124009005)
    ·
      refine ⟨6652365943453692046503377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17739642515876512124009005 6652365943453692046503377)
      ·
        refine ⟨4989274457590269034877533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6652365943453692046503377 4989274457590269034877533)
        ·
          refine ⟨1870977921596350888079075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4989274457590269034877533 1870977921596350888079075)
          ·
            refine ⟨2806466882394526332118613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1870977921596350888079075 2806466882394526332118613)
            ·
              refine ⟨32888283778060855454515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2806466882394526332118613 32888283778060855454515)
              ·
                rfl

theorem cell22_2594013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 8].length) (baseStart_2594013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2594013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2594013 prefixEnd_2594013 := by exact prefixLift 2594013
  have htrace : WordTrace (prefixWord ++ tailWord_2594013) baseStart_2594013 baseEnd_2594013 := by
    simpa [prefixWord, tailWord_2594013, baseEnd_2594013] using wordTrace_append hprefix tailTrace_2594013
  have hstable : (prefixWord ++ tailWord_2594013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594013).length < 2 ^ (prefixWord ++ tailWord_2594013).sum := by decide
  have hdescent : baseEnd_2594013 < baseStart_2594013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594024 : List Nat := [2, 1, 4, 1, 2, 1, 1, 3, 7]
def baseStart_2594024 : Nat := 118140960795 + 2594024 * 2 ^ 59
def prefixEnd_2594024 : Nat := 4983230072969 + 3 ^ 40 * 2594024 * 2
def baseEnd_2594024 : Nat := 295995809177480911748957

theorem tailTrace_2594024 : CollatzResearch.WordTrace tailWord_2594024 prefixEnd_2594024 295995809177480911748957 := by
  unfold tailWord_2594024
  simp only [CollatzResearch.WordTrace]
  refine ⟨47305913977150773436682563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63074551969534364582243417 47305913977150773436682563)
  ·
    refine ⟨70958870965726160155023845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47305913977150773436682563 70958870965726160155023845)
    ·
      refine ⟨13304788306073655029066971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70958870965726160155023845 13304788306073655029066971)
      ·
        refine ⟨19957182459110482543600457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13304788306073655029066971 19957182459110482543600457)
        ·
          refine ⟨14967886844332861907700343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19957182459110482543600457 14967886844332861907700343)
          ·
            refine ⟨22451830266499292861550515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14967886844332861907700343 22451830266499292861550515)
            ·
              refine ⟨33677745399748939292325773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22451830266499292861550515 33677745399748939292325773)
              ·
                refine ⟨12629154524905852234622165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33677745399748939292325773 12629154524905852234622165)
                ·
                  refine ⟨295995809177480911748957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12629154524905852234622165 295995809177480911748957)
                  ·
                    rfl

theorem cell22_2594024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 7].length) (baseStart_2594024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2594024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2594024 prefixEnd_2594024 := by exact prefixLift 2594024
  have htrace : WordTrace (prefixWord ++ tailWord_2594024) baseStart_2594024 baseEnd_2594024 := by
    simpa [prefixWord, tailWord_2594024, baseEnd_2594024] using wordTrace_append hprefix tailTrace_2594024
  have hstable : (prefixWord ++ tailWord_2594024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594024).length < 2 ^ (prefixWord ++ tailWord_2594024).sum := by decide
  have hdescent : baseEnd_2594024 < baseStart_2594024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594028 : List Nat := [2, 2, 1, 1, 2, 6, 1, 1, 3, 3]
def baseStart_2594028 : Nat := 118140960795 + 2594028 * 2 ^ 59
def prefixEnd_2594028 : Nat := 4983230072969 + 3 ^ 40 * 2594028 * 2
def baseEnd_2594028 : Nat := 887988796814188058146859

theorem tailTrace_2594028 : CollatzResearch.WordTrace tailWord_2594028 prefixEnd_2594028 887988796814188058146859 := by
  unfold tailWord_2594028
  simp only [CollatzResearch.WordTrace]
  refine ⟨47305986923143527778255369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63074649230858037037673825 47305986923143527778255369)
  ·
    refine ⟨35479490192357645833691527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47305986923143527778255369 35479490192357645833691527)
    ·
      refine ⟨53219235288536468750537291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35479490192357645833691527 53219235288536468750537291)
      ·
        refine ⟨79828852932804703125805937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53219235288536468750537291 79828852932804703125805937)
        ·
          refine ⟨59871639699603527344354453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79828852932804703125805937 59871639699603527344354453)
          ·
            refine ⟨2806483110918915344266615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 59871639699603527344354453 2806483110918915344266615)
            ·
              refine ⟨4209724666378373016399923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2806483110918915344266615 4209724666378373016399923)
              ·
                refine ⟨6314586999567559524599885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4209724666378373016399923 6314586999567559524599885)
                ·
                  refine ⟨2367970124837834821724957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6314586999567559524599885 2367970124837834821724957)
                  ·
                    refine ⟨887988796814188058146859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2367970124837834821724957 887988796814188058146859)
                    ·
                      rfl

theorem cell22_2594028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 3].length) (baseStart_2594028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2594028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2594028 prefixEnd_2594028 := by exact prefixLift 2594028
  have htrace : WordTrace (prefixWord ++ tailWord_2594028) baseStart_2594028 baseEnd_2594028 := by
    simpa [prefixWord, tailWord_2594028, baseEnd_2594028] using wordTrace_append hprefix tailTrace_2594028
  have hstable : (prefixWord ++ tailWord_2594028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594028).length < 2 ^ (prefixWord ++ tailWord_2594028).sum := by decide
  have hdescent : baseEnd_2594028 < baseStart_2594028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594079 : List Nat := [1, 1, 2, 4, 5, 1, 2, 2, 1, 3]
def baseStart_2594079 : Nat := 118140960795 + 2594079 * 2 ^ 59
def prefixEnd_2594079 : Nat := 4983230072969 + 3 ^ 40 * 2594079 * 2
def baseEnd_2594079 : Nat := 888006255156440925121703

theorem tailTrace_2594079 : CollatzResearch.WordTrace tailWord_2594079 prefixEnd_2594079 888006255156440925121703 := by
  unfold tailWord_2594079
  simp only [CollatzResearch.WordTrace]
  refine ⟨94613833969102291266617291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63075889312734860844411527 94613833969102291266617291)
  ·
    refine ⟨141920750953653436899925937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94613833969102291266617291 141920750953653436899925937)
    ·
      refine ⟨106440563215240077674944453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141920750953653436899925937 106440563215240077674944453)
      ·
        refine ⟨19957605602857514564052085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106440563215240077674944453 19957605602857514564052085)
        ·
          refine ⟨1871025525267891990379883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19957605602857514564052085 1871025525267891990379883)
          ·
            refine ⟨2806538287901837985569825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1871025525267891990379883 2806538287901837985569825)
            ·
              refine ⟨2104903715926378489177369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2806538287901837985569825 2104903715926378489177369)
              ·
                refine ⟨1578677786944783866883027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2104903715926378489177369 1578677786944783866883027)
                ·
                  refine ⟨2368016680417175800324541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1578677786944783866883027 2368016680417175800324541)
                  ·
                    refine ⟨888006255156440925121703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2368016680417175800324541 888006255156440925121703)
                    ·
                      rfl

theorem cell22_2594079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 2, 1, 3].length) (baseStart_2594079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2594079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2594079 prefixEnd_2594079 := by exact prefixLift 2594079
  have htrace : WordTrace (prefixWord ++ tailWord_2594079) baseStart_2594079 baseEnd_2594079 := by
    simpa [prefixWord, tailWord_2594079, baseEnd_2594079] using wordTrace_append hprefix tailTrace_2594079
  have hstable : (prefixWord ++ tailWord_2594079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594079).length < 2 ^ (prefixWord ++ tailWord_2594079).sum := by decide
  have hdescent : baseEnd_2594079 < baseStart_2594079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594101 : List Nat := [1, 3, 3, 1, 2, 2, 1, 3, 1, 5]
def baseStart_2594101 : Nat := 118140960795 + 2594101 * 2 ^ 59
def prefixEnd_2594101 : Nat := 4983230072969 + 3 ^ 40 * 2594101 * 2
def baseEnd_2594101 : Nat := 888013786206040201071635

theorem tailTrace_2594101 : CollatzResearch.WordTrace tailWord_2594101 prefixEnd_2594101 888013786206040201071635 := by
  unfold tailWord_2594101
  simp only [CollatzResearch.WordTrace]
  refine ⟨94614636375022589023918157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63076424250015059349278771 94614636375022589023918157)
  ·
    refine ⟨35480488640633470883969309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94614636375022589023918157 35480488640633470883969309)
    ·
      refine ⟨13305183240237551581488491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35480488640633470883969309 13305183240237551581488491)
      ·
        refine ⟨19957774860356327372232737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13305183240237551581488491 19957774860356327372232737)
        ·
          refine ⟨14968331145267245529174553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19957774860356327372232737 14968331145267245529174553)
          ·
            refine ⟨11226248358950434146880915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14968331145267245529174553 11226248358950434146880915)
            ·
              refine ⟨16839372538425651220321373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11226248358950434146880915 16839372538425651220321373)
              ·
                refine ⟨6314764701909619207620515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16839372538425651220321373 6314764701909619207620515)
                ·
                  refine ⟨9472147052864428811430773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6314764701909619207620515 9472147052864428811430773)
                  ·
                    refine ⟨888013786206040201071635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9472147052864428811430773 888013786206040201071635)
                    ·
                      rfl

theorem cell22_2594101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_2594101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2594101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2594101 prefixEnd_2594101 := by exact prefixLift 2594101
  have htrace : WordTrace (prefixWord ++ tailWord_2594101) baseStart_2594101 baseEnd_2594101 := by
    simpa [prefixWord, tailWord_2594101, baseEnd_2594101] using wordTrace_append hprefix tailTrace_2594101
  have hstable : (prefixWord ++ tailWord_2594101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594101).length < 2 ^ (prefixWord ++ tailWord_2594101).sum := by decide
  have hdescent : baseEnd_2594101 < baseStart_2594101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594135 : List Nat := [1, 1, 3, 2, 3, 4, 1, 2, 2, 3]
def baseStart_2594135 : Nat := 118140960795 + 2594135 * 2 ^ 59
def prefixEnd_2594135 : Nat := 4983230072969 + 3 ^ 40 * 2594135 * 2
def baseEnd_2594135 : Nat := 888025425100875445721531

theorem tailTrace_2594135 : CollatzResearch.WordTrace tailWord_2594135 prefixEnd_2594135 888025425100875445721531 := by
  unfold tailWord_2594135
  simp only [CollatzResearch.WordTrace]
  refine ⟨94615876456899412830655859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63077250971266275220437239 94615876456899412830655859)
  ·
    refine ⟨141923814685349119245983789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94615876456899412830655859 141923814685349119245983789)
    ·
      refine ⟨53221430507005919717243921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141923814685349119245983789 53221430507005919717243921)
      ·
        refine ⟨39916072880254439787932941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53221430507005919717243921 39916072880254439787932941)
        ·
          refine ⟨14968527330095414920474853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39916072880254439787932941 14968527330095414920474853)
          ·
            refine ⟨2806598874392890297589035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14968527330095414920474853 2806598874392890297589035)
            ·
              refine ⟨4209898311589335446383553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2806598874392890297589035 4209898311589335446383553)
              ·
                refine ⟨3157423733692001584787665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4209898311589335446383553 3157423733692001584787665)
                ·
                  refine ⟨2368067800269001188590749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3157423733692001584787665 2368067800269001188590749)
                  ·
                    refine ⟨888025425100875445721531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2368067800269001188590749 888025425100875445721531)
                    ·
                      rfl

theorem cell22_2594135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 2, 2, 3].length) (baseStart_2594135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2594135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2594135 prefixEnd_2594135 := by exact prefixLift 2594135
  have htrace : WordTrace (prefixWord ++ tailWord_2594135) baseStart_2594135 baseEnd_2594135 := by
    simpa [prefixWord, tailWord_2594135, baseEnd_2594135] using wordTrace_append hprefix tailTrace_2594135
  have hstable : (prefixWord ++ tailWord_2594135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594135).length < 2 ^ (prefixWord ++ tailWord_2594135).sum := by decide
  have hdescent : baseEnd_2594135 < baseStart_2594135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594152 : List Nat := [2, 1, 4, 2, 3, 1, 3, 1, 2, 3]
def baseStart_2594152 : Nat := 118140960795 + 2594152 * 2 ^ 59
def prefixEnd_2594152 : Nat := 4983230072969 + 3 ^ 40 * 2594152 * 2
def baseEnd_2594152 : Nat := 888031244548293068046479

theorem tailTrace_2594152 : CollatzResearch.WordTrace tailWord_2594152 prefixEnd_2594152 888031244548293068046479 := by
  unfold tailWord_2594152
  simp only [CollatzResearch.WordTrace]
  refine ⟨47308248248918912367012355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63077664331891883156016473 47308248248918912367012355)
  ·
    refine ⟨70962372373378368550518533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47308248248918912367012355 70962372373378368550518533)
    ·
      refine ⟨13305444820008444103222225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70962372373378368550518533 13305444820008444103222225)
      ·
        refine ⟨9979083615006333077416669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13305444820008444103222225 9979083615006333077416669)
        ·
          refine ⟨3742156355627374904031251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9979083615006333077416669 3742156355627374904031251)
          ·
            refine ⟨5613234533441062356046877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3742156355627374904031251 5613234533441062356046877)
            ·
              refine ⟨2104962950040398383517579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5613234533441062356046877 2104962950040398383517579)
              ·
                refine ⟨3157444425060597575276369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2104962950040398383517579 3157444425060597575276369)
                ·
                  refine ⟨2368083318795448181457277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3157444425060597575276369 2368083318795448181457277)
                  ·
                    refine ⟨888031244548293068046479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2368083318795448181457277 888031244548293068046479)
                    ·
                      rfl

theorem cell22_2594152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_2594152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2594152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2594152 prefixEnd_2594152 := by exact prefixLift 2594152
  have htrace : WordTrace (prefixWord ++ tailWord_2594152) baseStart_2594152 baseEnd_2594152 := by
    simpa [prefixWord, tailWord_2594152, baseEnd_2594152] using wordTrace_append hprefix tailTrace_2594152
  have hstable : (prefixWord ++ tailWord_2594152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594152).length < 2 ^ (prefixWord ++ tailWord_2594152).sum := by decide
  have hdescent : baseEnd_2594152 < baseStart_2594152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594165 : List Nat := [1, 3, 4, 1, 3, 2, 2, 6]
def baseStart_2594165 : Nat := 118140960795 + 2594165 * 2 ^ 59
def prefixEnd_2594165 : Nat := 4983230072969 + 3 ^ 40 * 2594165 * 2
def baseEnd_2594165 : Nat := 98670632745996151941271

theorem tailTrace_2594165 : CollatzResearch.WordTrace tailWord_2594165 prefixEnd_2594165 98670632745996151941271 := by
  unfold tailWord_2594165
  simp only [CollatzResearch.WordTrace]
  refine ⟨94616970646790727954247949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63077980431193818636165299 94616970646790727954247949)
  ·
    refine ⟨35481363992546522982842981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94616970646790727954247949 35481363992546522982842981)
    ·
      refine ⟨6652755748602473059283059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35481363992546522982842981 6652755748602473059283059)
      ·
        refine ⟨9979133622903709588924589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6652755748602473059283059 9979133622903709588924589)
        ·
          refine ⟨3742175108588891095846721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9979133622903709588924589 3742175108588891095846721)
          ·
            refine ⟨2806631331441668321885041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3742175108588891095846721 2806631331441668321885041)
            ·
              refine ⟨2104973498581251241413781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2806631331441668321885041 2104973498581251241413781)
              ·
                refine ⟨98670632745996151941271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2104973498581251241413781 98670632745996151941271)
                ·
                  rfl

theorem cell22_2594165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 6].length) (baseStart_2594165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2594165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2594165 prefixEnd_2594165 := by exact prefixLift 2594165
  have htrace : WordTrace (prefixWord ++ tailWord_2594165) baseStart_2594165 baseEnd_2594165 := by
    simpa [prefixWord, tailWord_2594165, baseEnd_2594165] using wordTrace_append hprefix tailTrace_2594165
  have hstable : (prefixWord ++ tailWord_2594165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594165).length < 2 ^ (prefixWord ++ tailWord_2594165).sum := by decide
  have hdescent : baseEnd_2594165 < baseStart_2594165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594210 : List Nat := [3, 3, 1, 2, 1, 2, 4, 1, 5]
def baseStart_2594210 : Nat := 118140960795 + 2594210 * 2 ^ 59
def prefixEnd_2594210 : Nat := 4983230072969 + 3 ^ 40 * 2594210 * 2
def baseEnd_2594210 : Nat := 296017033044533416698767

theorem tailTrace_2594210 : CollatzResearch.WordTrace tailWord_2594210 prefixEnd_2594210 296017033044533416698767 := by
  unfold tailWord_2594210
  simp only [CollatzResearch.WordTrace]
  refine ⟨23654652982906925159909021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63079074621085133759757389 23654652982906925159909021)
  ·
    refine ⟨8870494868590096934965883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23654652982906925159909021 8870494868590096934965883)
    ·
      refine ⟨13305742302885145402448825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8870494868590096934965883 13305742302885145402448825)
      ·
        refine ⟨9979306727163859051836619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13305742302885145402448825 9979306727163859051836619)
        ·
          refine ⟨14968960090745788577754929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9979306727163859051836619 14968960090745788577754929)
          ·
            refine ⟨11226720068059341433316197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14968960090745788577754929 11226720068059341433316197)
            ·
              refine ⟨2105010012761126518746787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11226720068059341433316197 2105010012761126518746787)
              ·
                refine ⟨3157515019141689778120181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2105010012761126518746787 3157515019141689778120181)
                ·
                  refine ⟨296017033044533416698767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3157515019141689778120181 296017033044533416698767)
                  ·
                    rfl

theorem cell22_2594210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_2594210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2594210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2594210 prefixEnd_2594210 := by exact prefixLift 2594210
  have htrace : WordTrace (prefixWord ++ tailWord_2594210) baseStart_2594210 baseEnd_2594210 := by
    simpa [prefixWord, tailWord_2594210, baseEnd_2594210] using wordTrace_append hprefix tailTrace_2594210
  have hstable : (prefixWord ++ tailWord_2594210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594210).length < 2 ^ (prefixWord ++ tailWord_2594210).sum := by decide
  have hdescent : baseEnd_2594210 < baseStart_2594210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594255 : List Nat := [1, 1, 2, 1, 1, 4, 6, 2, 4]
def baseStart_2594255 : Nat := 118140960795 + 2594255 * 2 ^ 59
def prefixEnd_2594255 : Nat := 4983230072969 + 3 ^ 40 * 2594255 * 2
def baseEnd_2594255 : Nat := 296022167851078377573721

theorem tailTrace_2594255 : CollatzResearch.WordTrace tailWord_2594255 prefixEnd_2594255 296022167851078377573721 := by
  unfold tailWord_2594255
  simp only [CollatzResearch.WordTrace]
  refine ⟨94620253216464673325024219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63080168810976448883349479 94620253216464673325024219)
  ·
    refine ⟨141930379824697009987536329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94620253216464673325024219 141930379824697009987536329)
    ·
      refine ⟨106447784868522757490652247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141930379824697009987536329 106447784868522757490652247)
      ·
        refine ⟨159671677302784136235978371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106447784868522757490652247 159671677302784136235978371)
        ·
          refine ⟨239507515954176204353967557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159671677302784136235978371 239507515954176204353967557)
          ·
            refine ⟨44907659241408038316368917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 239507515954176204353967557 44907659241408038316368917)
            ·
              refine ⟨2105046526941001796079793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 44907659241408038316368917 2105046526941001796079793)
              ·
                refine ⟨1578784895205751347059845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2105046526941001796079793 1578784895205751347059845)
                ·
                  refine ⟨296022167851078377573721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1578784895205751347059845 296022167851078377573721)
                  ·
                    rfl

theorem cell22_2594255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 2, 4].length) (baseStart_2594255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2594255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2594255 prefixEnd_2594255 := by exact prefixLift 2594255
  have htrace : WordTrace (prefixWord ++ tailWord_2594255) baseStart_2594255 baseEnd_2594255 := by
    simpa [prefixWord, tailWord_2594255, baseEnd_2594255] using wordTrace_append hprefix tailTrace_2594255
  have hstable : (prefixWord ++ tailWord_2594255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594255).length < 2 ^ (prefixWord ++ tailWord_2594255).sum := by decide
  have hdescent : baseEnd_2594255 < baseStart_2594255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594285 : List Nat := [1, 5, 1, 3, 2, 1, 1, 1, 1, 6]
def baseStart_2594285 : Nat := 118140960795 + 2594285 * 2 ^ 59
def prefixEnd_2594285 : Nat := 4983230072969 + 3 ^ 40 * 2594285 * 2
def baseEnd_2594285 : Nat := 888076773166325054471071

theorem tailTrace_2594285 : CollatzResearch.WordTrace tailWord_2594285 prefixEnd_2594285 888076773166325054471071 := by
  unfold tailWord_2594285
  simp only [CollatzResearch.WordTrace]
  refine ⟨94621347406355988448616309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63080898270903992299077539 94621347406355988448616309)
  ·
    refine ⟨8870751319345873917057779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94621347406355988448616309 8870751319345873917057779)
    ·
      refine ⟨13306126979018810875586669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8870751319345873917057779 13306126979018810875586669)
      ·
        refine ⟨4989797617132054078345001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13306126979018810875586669 4989797617132054078345001)
        ·
          refine ⟨3742348212849040558758751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4989797617132054078345001 3742348212849040558758751)
          ·
            refine ⟨5613522319273560838138127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3742348212849040558758751 5613522319273560838138127)
            ·
              refine ⟨8420283478910341257207191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5613522319273560838138127 8420283478910341257207191)
              ·
                refine ⟨12630425218365511885810787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8420283478910341257207191 12630425218365511885810787)
                ·
                  refine ⟨18945637827548267828716181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12630425218365511885810787 18945637827548267828716181)
                  ·
                    refine ⟨888076773166325054471071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18945637827548267828716181 888076773166325054471071)
                    ·
                      rfl

theorem cell22_2594285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_2594285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2594285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2594285 prefixEnd_2594285 := by exact prefixLift 2594285
  have htrace : WordTrace (prefixWord ++ tailWord_2594285) baseStart_2594285 baseEnd_2594285 := by
    simpa [prefixWord, tailWord_2594285, baseEnd_2594285] using wordTrace_append hprefix tailTrace_2594285
  have hstable : (prefixWord ++ tailWord_2594285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594285).length < 2 ^ (prefixWord ++ tailWord_2594285).sum := by decide
  have hdescent : baseEnd_2594285 < baseStart_2594285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594298 : List Nat := [3, 1, 1, 1, 1, 2, 3, 2, 5, 3]
def baseStart_2594298 : Nat := 118140960795 + 2594298 * 2 ^ 59
def prefixEnd_2594298 : Nat := 4983230072969 + 3 ^ 40 * 2594298 * 2
def baseEnd_2594298 : Nat := 888081223331997353896031

theorem tailTrace_2594298 : CollatzResearch.WordTrace tailWord_2594298 prefixEnd_2594298 888081223331997353896031 := by
  unfold tailWord_2594298
  simp only [CollatzResearch.WordTrace]
  refine ⟨23655455388827222917209887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63081214370205927779226365 23655455388827222917209887)
  ·
    refine ⟨35483183083240834375814831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23655455388827222917209887 35483183083240834375814831)
    ·
      refine ⟨53224774624861251563722247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35483183083240834375814831 53224774624861251563722247)
      ·
        refine ⟨79837161937291877345583371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53224774624861251563722247 79837161937291877345583371)
        ·
          refine ⟨119755742905937816018375057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79837161937291877345583371 119755742905937816018375057)
          ·
            refine ⟨89816807179453362013781293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119755742905937816018375057 89816807179453362013781293)
            ·
              refine ⟨33681302692295010755167985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89816807179453362013781293 33681302692295010755167985)
              ·
                refine ⟨25260977019221258066375989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33681302692295010755167985 25260977019221258066375989)
                ·
                  refine ⟨2368216595551992943722749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25260977019221258066375989 2368216595551992943722749)
                  ·
                    refine ⟨888081223331997353896031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2368216595551992943722749 888081223331997353896031)
                    ·
                      rfl

theorem cell22_2594298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 5, 3].length) (baseStart_2594298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2594298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2594298 prefixEnd_2594298 := by exact prefixLift 2594298
  have htrace : WordTrace (prefixWord ++ tailWord_2594298) baseStart_2594298 baseEnd_2594298 := by
    simpa [prefixWord, tailWord_2594298, baseEnd_2594298] using wordTrace_append hprefix tailTrace_2594298
  have hstable : (prefixWord ++ tailWord_2594298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594298).length < 2 ^ (prefixWord ++ tailWord_2594298).sum := by decide
  have hdescent : baseEnd_2594298 < baseStart_2594298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594334 : List Nat := [4, 3, 3, 1, 1, 1, 1, 8]
def baseStart_2594334 : Nat := 118140960795 + 2594334 * 2 ^ 59
def prefixEnd_2594334 : Nat := 4983230072969 + 3 ^ 40 * 2594334 * 2
def baseEnd_2594334 : Nat := 98677060763078362221769

theorem tailTrace_2594334 : CollatzResearch.WordTrace tailWord_2594334 prefixEnd_2594334 98677060763078362221769 := by
  unfold tailWord_2594334
  simp only [CollatzResearch.WordTrace]
  refine ⟨11827891822897308727143757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63082089722118979878100037 11827891822897308727143757)
  ·
    refine ⟨4435459433586490772678909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11827891822897308727143757 4435459433586490772678909)
    ·
      refine ⟨1663297287594934039754591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4435459433586490772678909 1663297287594934039754591)
      ·
        refine ⟨2494945931392401059631887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1663297287594934039754591 2494945931392401059631887)
        ·
          refine ⟨3742418897088601589447831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2494945931392401059631887 3742418897088601589447831)
          ·
            refine ⟨5613628345632902384171747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3742418897088601589447831 5613628345632902384171747)
            ·
              refine ⟨8420442518449353576257621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5613628345632902384171747 8420442518449353576257621)
              ·
                refine ⟨98677060763078362221769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8420442518449353576257621 98677060763078362221769)
                ·
                  rfl

theorem cell22_2594334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 8].length) (baseStart_2594334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2594334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2594334 prefixEnd_2594334 := by exact prefixLift 2594334
  have htrace : WordTrace (prefixWord ++ tailWord_2594334) baseStart_2594334 baseEnd_2594334 := by
    simpa [prefixWord, tailWord_2594334, baseEnd_2594334] using wordTrace_append hprefix tailTrace_2594334
  have hstable : (prefixWord ++ tailWord_2594334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594334).length < 2 ^ (prefixWord ++ tailWord_2594334).sum := by decide
  have hdescent : baseEnd_2594334 < baseStart_2594334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594405 : List Nat := [1, 3, 1, 3, 3, 2, 1, 2, 1, 5]
def baseStart_2594405 : Nat := 118140960795 + 2594405 * 2 ^ 59
def prefixEnd_2594405 : Nat := 4983230072969 + 3 ^ 40 * 2594405 * 2
def baseEnd_2594405 : Nat := 888117851618684741470703

theorem tailTrace_2594405 : CollatzResearch.WordTrace tailWord_2594405 prefixEnd_2594405 888117851618684741470703 := by
  unfold tailWord_2594405
  simp only [CollatzResearch.WordTrace]
  refine ⟨94625724165921248942984669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63083816110614165961989779 94625724165921248942984669)
  ·
    refine ⟨35484646562220468353619251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94625724165921248942984669 35484646562220468353619251)
    ·
      refine ⟨53226969843330702530428877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35484646562220468353619251 53226969843330702530428877)
      ·
        refine ⟨19960113691249013448910829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53226969843330702530428877 19960113691249013448910829)
        ·
          refine ⟨7485042634218380043341561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19960113691249013448910829 7485042634218380043341561)
          ·
            refine ⟨5613781975663785032506171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7485042634218380043341561 5613781975663785032506171)
            ·
              refine ⟨8420672963495677548759257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5613781975663785032506171 8420672963495677548759257)
              ·
                refine ⟨6315504722621758161569443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8420672963495677548759257 6315504722621758161569443)
                ·
                  refine ⟨9473257083932637242354165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6315504722621758161569443 9473257083932637242354165)
                  ·
                    refine ⟨888117851618684741470703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9473257083932637242354165 888117851618684741470703)
                    ·
                      rfl

theorem cell22_2594405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 5].length) (baseStart_2594405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2594405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2594405 prefixEnd_2594405 := by exact prefixLift 2594405
  have htrace : WordTrace (prefixWord ++ tailWord_2594405) baseStart_2594405 baseEnd_2594405 := by
    simpa [prefixWord, tailWord_2594405, baseEnd_2594405] using wordTrace_append hprefix tailTrace_2594405
  have hstable : (prefixWord ++ tailWord_2594405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594405).length < 2 ^ (prefixWord ++ tailWord_2594405).sum := by decide
  have hdescent : baseEnd_2594405 < baseStart_2594405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594418 : List Nat := [3, 2, 1, 2, 3, 11]
def baseStart_2594418 : Nat := 118140960795 + 2594418 * 2 ^ 59
def prefixEnd_2594418 : Nat := 4983230072969 + 3 ^ 40 * 2594418 * 2
def baseEnd_2594418 : Nat := 10964472861535272109823

theorem tailTrace_2594418 : CollatzResearch.WordTrace tailWord_2594418 prefixEnd_2594418 10964472861535272109823 := by
  unfold tailWord_2594418
  simp only [CollatzResearch.WordTrace]
  refine ⟨23656549578718538040801977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63084132209916101442138605 23656549578718538040801977)
  ·
    refine ⟨17742412184038903530601483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23656549578718538040801977 17742412184038903530601483)
    ·
      refine ⟨26613618276058355295902225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17742412184038903530601483 26613618276058355295902225)
      ·
        refine ⟨19960213707043766471926669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26613618276058355295902225 19960213707043766471926669)
        ·
          refine ⟨7485080140141412426972501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19960213707043766471926669 7485080140141412426972501)
          ·
            refine ⟨10964472861535272109823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7485080140141412426972501 10964472861535272109823)
            ·
              rfl

theorem cell22_2594418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 11].length) (baseStart_2594418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2594418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2594418 prefixEnd_2594418 := by exact prefixLift 2594418
  have htrace : WordTrace (prefixWord ++ tailWord_2594418) baseStart_2594418 baseEnd_2594418 := by
    simpa [prefixWord, tailWord_2594418, baseEnd_2594418] using wordTrace_append hprefix tailTrace_2594418
  have hstable : (prefixWord ++ tailWord_2594418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594418).length < 2 ^ (prefixWord ++ tailWord_2594418).sum := by decide
  have hdescent : baseEnd_2594418 < baseStart_2594418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594480 : List Nat := [2, 1, 1, 1, 2, 1, 7, 2, 5]
def baseStart_2594480 : Nat := 118140960795 + 2594480 * 2 ^ 59
def prefixEnd_2594480 : Nat := 4983230072969 + 3 ^ 40 * 2594480 * 2
def baseEnd_2594480 : Nat := 296047841883803181948491

theorem tailTrace_2594480 : CollatzResearch.WordTrace tailWord_2594480 prefixEnd_2594480 296047841883803181948491 := by
  unfold tailWord_2594480
  simp only [CollatzResearch.WordTrace]
  refine ⟨47314229820324768375982447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63085639760433024501309929 47314229820324768375982447)
  ·
    refine ⟨70971344730487152563973671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47314229820324768375982447 70971344730487152563973671)
    ·
      refine ⟨106457017095730728845960507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70971344730487152563973671 106457017095730728845960507)
      ·
        refine ⟨159685525643596093268940761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106457017095730728845960507 159685525643596093268940761)
        ·
          refine ⟨119764144232697069951705571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159685525643596093268940761 119764144232697069951705571)
          ·
            refine ⟨179646216349045604927558357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119764144232697069951705571 179646216349045604927558357)
            ·
              refine ⟨4210458195680756365489649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 179646216349045604927558357 4210458195680756365489649)
              ·
                refine ⟨3157843646760567274117237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4210458195680756365489649 3157843646760567274117237)
                ·
                  refine ⟨296047841883803181948491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3157843646760567274117237 296047841883803181948491)
                  ·
                    rfl

theorem cell22_2594480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 2, 5].length) (baseStart_2594480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2594480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2594480 prefixEnd_2594480 := by exact prefixLift 2594480
  have htrace : WordTrace (prefixWord ++ tailWord_2594480) baseStart_2594480 baseEnd_2594480 := by
    simpa [prefixWord, tailWord_2594480, baseEnd_2594480] using wordTrace_append hprefix tailTrace_2594480
  have hstable : (prefixWord ++ tailWord_2594480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594480).length < 2 ^ (prefixWord ++ tailWord_2594480).sum := by decide
  have hdescent : baseEnd_2594480 < baseStart_2594480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594548 : List Nat := [2, 6, 1, 1, 1, 3, 2, 1, 5]
def baseStart_2594548 : Nat := 118140960795 + 2594548 * 2 ^ 59
def prefixEnd_2594548 : Nat := 4983230072969 + 3 ^ 40 * 2594548 * 2
def baseEnd_2594548 : Nat := 296055601147026678381755

theorem tailTrace_2594548 : CollatzResearch.WordTrace tailWord_2594548 prefixEnd_2594548 296055601147026678381755 := by
  unfold tailWord_2594548
  simp only [CollatzResearch.WordTrace]
  refine ⟨47315469902201592182720149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63087293202935456243626865 47315469902201592182720149)
  ·
    refine ⟨2217912651665699633565007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 47315469902201592182720149 2217912651665699633565007)
    ·
      refine ⟨3326868977498549450347511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2217912651665699633565007 3326868977498549450347511)
      ·
        refine ⟨4990303466247824175521267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3326868977498549450347511 4990303466247824175521267)
        ·
          refine ⟨7485455199371736263281901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4990303466247824175521267 7485455199371736263281901)
          ·
            refine ⟨2807045699764401098730713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7485455199371736263281901 2807045699764401098730713)
            ·
              refine ⟨2105284274823300824048035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2807045699764401098730713 2105284274823300824048035)
              ·
                refine ⟨3157926412234951236072053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2105284274823300824048035 3157926412234951236072053)
                ·
                  refine ⟨296055601147026678381755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3157926412234951236072053 296055601147026678381755)
                  ·
                    rfl

theorem cell22_2594548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_2594548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2594548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2594548 prefixEnd_2594548 := by exact prefixLift 2594548
  have htrace : WordTrace (prefixWord ++ tailWord_2594548) baseStart_2594548 baseEnd_2594548 := by
    simpa [prefixWord, tailWord_2594548, baseEnd_2594548] using wordTrace_append hprefix tailTrace_2594548
  have hstable : (prefixWord ++ tailWord_2594548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594548).length < 2 ^ (prefixWord ++ tailWord_2594548).sum := by decide
  have hdescent : baseEnd_2594548 < baseStart_2594548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594570 : List Nat := [3, 1, 2, 2, 1, 3, 2, 8]
def baseStart_2594570 : Nat := 118140960795 + 2594570 * 2 ^ 59
def prefixEnd_2594570 : Nat := 4983230072969 + 3 ^ 40 * 2594570 * 2
def baseEnd_2594570 : Nat := 98686037165631034566133

theorem tailTrace_2594570 : CollatzResearch.WordTrace tailWord_2594570 prefixEnd_2594570 98686037165631034566133 := by
  unfold tailWord_2594570
  simp only [CollatzResearch.WordTrace]
  refine ⟨23657935552580870530685291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63087828140215654748494109 23657935552580870530685291)
  ·
    refine ⟨35486903328871305796027937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23657935552580870530685291 35486903328871305796027937)
    ·
      refine ⟨26615177496653479347020953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35486903328871305796027937 26615177496653479347020953)
      ·
        refine ⟨19961383122490109510265715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26615177496653479347020953 19961383122490109510265715)
        ·
          refine ⟨29942074683735164265398573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19961383122490109510265715 29942074683735164265398573)
          ·
            refine ⟨11228278006400686599524465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29942074683735164265398573 11228278006400686599524465)
            ·
              refine ⟨8421208504800514949643349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11228278006400686599524465 8421208504800514949643349)
              ·
                refine ⟨98686037165631034566133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8421208504800514949643349 98686037165631034566133)
                ·
                  rfl

theorem cell22_2594570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 8].length) (baseStart_2594570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2594570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2594570 prefixEnd_2594570 := by exact prefixLift 2594570
  have htrace : WordTrace (prefixWord ++ tailWord_2594570) baseStart_2594570 baseEnd_2594570 := by
    simpa [prefixWord, tailWord_2594570, baseEnd_2594570] using wordTrace_append hprefix tailTrace_2594570
  have hstable : (prefixWord ++ tailWord_2594570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594570).length < 2 ^ (prefixWord ++ tailWord_2594570).sum := by decide
  have hdescent : baseEnd_2594570 < baseStart_2594570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594677 : List Nat := [1, 3, 4, 1, 1, 1, 1, 4, 6]
def baseStart_2594677 : Nat := 118140960795 + 2594677 * 2 ^ 59
def prefixEnd_2594677 : Nat := 4983230072969 + 3 ^ 40 * 2594677 * 2
def baseEnd_2594677 : Nat := 296070320925788899556623

theorem tailTrace_2594677 : CollatzResearch.WordTrace tailWord_2594677 prefixEnd_2594677 296070320925788899556623 := by
  unfold tailWord_2594677
  simp only [CollatzResearch.WordTrace]
  refine ⟨94635644820935839396886285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63090429880623892931257523 94635644820935839396886285)
  ·
    refine ⟨35488366807850939773832357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94635644820935839396886285 35488366807850939773832357)
    ·
      refine ⟨6654068776472051207593567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35488366807850939773832357 6654068776472051207593567)
      ·
        refine ⟨9981103164708076811390351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6654068776472051207593567 9981103164708076811390351)
        ·
          refine ⟨14971654747062115217085527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9981103164708076811390351 14971654747062115217085527)
          ·
            refine ⟨22457482120593172825628291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14971654747062115217085527 22457482120593172825628291)
            ·
              refine ⟨33686223180889759238442437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22457482120593172825628291 33686223180889759238442437)
              ·
                refine ⟨6316166846416829857207957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33686223180889759238442437 6316166846416829857207957)
                ·
                  refine ⟨296070320925788899556623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6316166846416829857207957 296070320925788899556623)
                  ·
                    rfl

theorem cell22_2594677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 6].length) (baseStart_2594677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2594677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2594677 prefixEnd_2594677 := by exact prefixLift 2594677
  have htrace : WordTrace (prefixWord ++ tailWord_2594677) baseStart_2594677 baseEnd_2594677 := by
    simpa [prefixWord, tailWord_2594677, baseEnd_2594677] using wordTrace_append hprefix tailTrace_2594677
  have hstable : (prefixWord ++ tailWord_2594677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594677).length < 2 ^ (prefixWord ++ tailWord_2594677).sum := by decide
  have hdescent : baseEnd_2594677 < baseStart_2594677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
