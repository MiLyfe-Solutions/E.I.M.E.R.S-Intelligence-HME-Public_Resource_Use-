import V185TrunkScan23Chunk0359

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2129631 : List Nat := [1, 1, 2, 3, 2, 2, 1, 2, 3, 6]
def baseStart_2129631 : Nat := 118140960795 + 2129631 * 2 ^ 59
def prefixEnd_2129631 : Nat := 4983230072969 + 3 ^ 40 * 2129631 * 2
def baseEnd_2129631 : Nat := 364508106571754180872837

theorem tailTrace_2129631 : CollatzResearch.WordTrace tailWord_2129631 prefixEnd_2129631 364508106571754180872837 := by
  unfold tailWord_2129631
  simp only [CollatzResearch.WordTrace]
  refine ⟨77674023747718073863316747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51782682498478715908877831 77674023747718073863316747)
  ·
    refine ⟨116511035621577110794975121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77674023747718073863316747 116511035621577110794975121)
    ·
      refine ⟨87383276716182833096231341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116511035621577110794975121 87383276716182833096231341)
      ·
        refine ⟨32768728768568562411086753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87383276716182833096231341 32768728768568562411086753)
        ·
          refine ⟨24576546576426421808315065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32768728768568562411086753 24576546576426421808315065)
          ·
            refine ⟨18432409932319816356236299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24576546576426421808315065 18432409932319816356236299)
            ·
              refine ⟨27648614898479724534354449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18432409932319816356236299 27648614898479724534354449)
              ·
                refine ⟨20736461173859793400765837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27648614898479724534354449 20736461173859793400765837)
                ·
                  refine ⟨7776172940197422525287189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20736461173859793400765837 7776172940197422525287189)
                  ·
                    refine ⟨364508106571754180872837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7776172940197422525287189 364508106571754180872837)
                    ·
                      rfl

theorem cell23_2129631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 6].length) (baseStart_2129631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129631 prefixEnd_2129631 := by exact prefixLift 2129631
  have htrace : WordTrace (prefixWord ++ tailWord_2129631) baseStart_2129631 baseEnd_2129631 := by
    simpa [prefixWord, tailWord_2129631, baseEnd_2129631] using wordTrace_append hprefix tailTrace_2129631
  have hstable : (prefixWord ++ tailWord_2129631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129631).length < 2 ^ (prefixWord ++ tailWord_2129631).sum := by decide
  have hdescent : baseEnd_2129631 < baseStart_2129631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129641 : List Nat := [1, 2, 1, 1, 1, 2, 3, 3, 3, 1, 5]
def baseStart_2129641 : Nat := 118140960795 + 2129641 * 2 ^ 59
def prefixEnd_2129641 : Nat := 4983230072969 + 3 ^ 40 * 2129641 * 2
def baseEnd_2129641 : Nat := 1093529454521807503493465

theorem tailTrace_2129641 : CollatzResearch.WordTrace tailWord_2129641 prefixEnd_2129641 1093529454521807503493465 := by
  unfold tailWord_2129641
  simp only [CollatzResearch.WordTrace]
  refine ⟨77674388477681845571180777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51782925651787897047453851 77674388477681845571180777)
  ·
    refine ⟨58255791358261384178385583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77674388477681845571180777 58255791358261384178385583)
    ·
      refine ⟨87383687037392076267578375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58255791358261384178385583 87383687037392076267578375)
      ·
        refine ⟨131075530556088114401367563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87383687037392076267578375 131075530556088114401367563)
        ·
          refine ⟨196613295834132171602051345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131075530556088114401367563 196613295834132171602051345)
          ·
            refine ⟨147459971875599128701538509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196613295834132171602051345 147459971875599128701538509)
            ·
              refine ⟨55297489453349673263076941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 147459971875599128701538509 55297489453349673263076941)
              ·
                refine ⟨20736558545006127473653853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55297489453349673263076941 20736558545006127473653853)
                ·
                  refine ⟨7776209454377297802620195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20736558545006127473653853 7776209454377297802620195)
                  ·
                    refine ⟨11664314181565946703930293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7776209454377297802620195 11664314181565946703930293)
                    ·
                      refine ⟨1093529454521807503493465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11664314181565946703930293 1093529454521807503493465)
                      ·
                        rfl

theorem cell23_2129641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 1, 5].length) (baseStart_2129641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129641 prefixEnd_2129641 := by exact prefixLift 2129641
  have htrace : WordTrace (prefixWord ++ tailWord_2129641) baseStart_2129641 baseEnd_2129641 := by
    simpa [prefixWord, tailWord_2129641, baseEnd_2129641] using wordTrace_append hprefix tailTrace_2129641
  have hstable : (prefixWord ++ tailWord_2129641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129641).length < 2 ^ (prefixWord ++ tailWord_2129641).sum := by decide
  have hdescent : baseEnd_2129641 < baseStart_2129641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129651 : List Nat := [1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 6]
def baseStart_2129651 : Nat := 118140960795 + 2129651 * 2 ^ 59
def prefixEnd_2129651 : Nat := 4983230072969 + 3 ^ 40 * 2129651 * 2
def baseEnd_2129651 : Nat := 1093534589328352464368419

theorem tailTrace_2129651 : CollatzResearch.WordTrace tailWord_2129651 prefixEnd_2129651 1093534589328352464368419 := by
  unfold tailWord_2129651
  simp only [CollatzResearch.WordTrace]
  refine ⟨77674753207645617279044807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51783168805097078186029871 77674753207645617279044807)
  ·
    refine ⟨116512129811468425918567211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77674753207645617279044807 116512129811468425918567211)
    ·
      refine ⟨174768194717202638877850817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116512129811468425918567211 174768194717202638877850817)
      ·
        refine ⟨131076146037901979158388113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174768194717202638877850817 131076146037901979158388113)
        ·
          refine ⟨98307109528426484368791085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131076146037901979158388113 98307109528426484368791085)
          ·
            refine ⟨36865166073159931638296657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98307109528426484368791085 36865166073159931638296657)
            ·
              refine ⟨27648874554869948728722493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36865166073159931638296657 27648874554869948728722493)
              ·
                refine ⟨10368327958076230773270935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27648874554869948728722493 10368327958076230773270935)
                ·
                  refine ⟨15552491937114346159906403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10368327958076230773270935 15552491937114346159906403)
                  ·
                    refine ⟨23328737905671519239859605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15552491937114346159906403 23328737905671519239859605)
                    ·
                      refine ⟨1093534589328352464368419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23328737905671519239859605 1093534589328352464368419)
                      ·
                        rfl

theorem cell23_2129651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 6].length) (baseStart_2129651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129651 prefixEnd_2129651 := by exact prefixLift 2129651
  have htrace : WordTrace (prefixWord ++ tailWord_2129651) baseStart_2129651 baseEnd_2129651 := by
    simpa [prefixWord, tailWord_2129651, baseEnd_2129651] using wordTrace_append hprefix tailTrace_2129651
  have hstable : (prefixWord ++ tailWord_2129651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129651).length < 2 ^ (prefixWord ++ tailWord_2129651).sum := by decide
  have hdescent : baseEnd_2129651 < baseStart_2129651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129652 : List Nat := [2, 6, 1, 1, 1, 1, 2, 1, 3, 5]
def baseStart_2129652 : Nat := 118140960795 + 2129652 * 2 ^ 59
def prefixEnd_2129652 : Nat := 4983230072969 + 3 ^ 40 * 2129652 * 2
def baseEnd_2129652 : Nat := 364511700936335653485305

theorem tailTrace_2129652 : CollatzResearch.WordTrace tailWord_2129652 prefixEnd_2129652 364511700936335653485305 := by
  unfold tailWord_2129652
  simp only [CollatzResearch.WordTrace]
  refine ⟨38837394840320997224915605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51783193120427996299887473 38837394840320997224915605)
  ·
    refine ⟨1820502883140046744917919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 38837394840320997224915605 1820502883140046744917919)
    ·
      refine ⟨2730754324710070117376879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1820502883140046744917919 2730754324710070117376879)
      ·
        refine ⟨4096131487065105176065319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2730754324710070117376879 4096131487065105176065319)
        ·
          refine ⟨6144197230597657764097979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4096131487065105176065319 6144197230597657764097979)
          ·
            refine ⟨9216295845896486646146969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6144197230597657764097979 9216295845896486646146969)
            ·
              refine ⟨6912221884422364984610227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9216295845896486646146969 6912221884422364984610227)
              ·
                refine ⟨10368332826633547476915341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6912221884422364984610227 10368332826633547476915341)
                ·
                  refine ⟨3888124809987580303843253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10368332826633547476915341 3888124809987580303843253)
                  ·
                    refine ⟨364511700936335653485305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3888124809987580303843253 364511700936335653485305)
                    ·
                      rfl

theorem cell23_2129652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_2129652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129652 prefixEnd_2129652 := by exact prefixLift 2129652
  have htrace : WordTrace (prefixWord ++ tailWord_2129652) baseStart_2129652 baseEnd_2129652 := by
    simpa [prefixWord, tailWord_2129652, baseEnd_2129652] using wordTrace_append hprefix tailTrace_2129652
  have hstable : (prefixWord ++ tailWord_2129652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129652).length < 2 ^ (prefixWord ++ tailWord_2129652).sum := by decide
  have hdescent : baseEnd_2129652 < baseStart_2129652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129655 : List Nat := [1, 1, 3, 1, 1, 1, 5, 1, 5, 2, 2]
def baseStart_2129655 : Nat := 118140960795 + 2129655 * 2 ^ 59
def prefixEnd_2129655 : Nat := 4983230072969 + 3 ^ 40 * 2129655 * 2
def baseEnd_2129655 : Nat := 1093536643250970448718401

theorem tailTrace_2129655 : CollatzResearch.WordTrace tailWord_2129655 prefixEnd_2129655 1093536643250970448718401 := by
  unfold tailWord_2129655
  simp only [CollatzResearch.WordTrace]
  refine ⟨77674899099631125962190419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51783266066420750641460279 77674899099631125962190419)
  ·
    refine ⟨116512348649446688943285629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77674899099631125962190419 116512348649446688943285629)
    ·
      refine ⟨43692130743542508353732111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116512348649446688943285629 43692130743542508353732111)
      ·
        refine ⟨65538196115313762530598167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43692130743542508353732111 65538196115313762530598167)
        ·
          refine ⟨98307294172970643795897251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65538196115313762530598167 98307294172970643795897251)
          ·
            refine ⟨147460941259455965693845877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98307294172970643795897251 147460941259455965693845877)
            ·
              refine ⟨13824463243073996783798051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 147460941259455965693845877 13824463243073996783798051)
              ·
                refine ⟨20736694864610995175697077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13824463243073996783798051 20736694864610995175697077)
                ·
                  refine ⟨1944065143557280797721601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20736694864610995175697077 1944065143557280797721601)
                  ·
                    refine ⟨1458048857667960598291201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1944065143557280797721601 1458048857667960598291201)
                    ·
                      refine ⟨1093536643250970448718401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1458048857667960598291201 1093536643250970448718401)
                      ·
                        rfl

theorem cell23_2129655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 5, 2, 2].length) (baseStart_2129655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129655 prefixEnd_2129655 := by exact prefixLift 2129655
  have htrace : WordTrace (prefixWord ++ tailWord_2129655) baseStart_2129655 baseEnd_2129655 := by
    simpa [prefixWord, tailWord_2129655, baseEnd_2129655] using wordTrace_append hprefix tailTrace_2129655
  have hstable : (prefixWord ++ tailWord_2129655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129655).length < 2 ^ (prefixWord ++ tailWord_2129655).sum := by decide
  have hdescent : baseEnd_2129655 < baseStart_2129655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129681 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 6]
def baseStart_2129681 : Nat := 118140960795 + 2129681 * 2 ^ 59
def prefixEnd_2129681 : Nat := 4983230072969 + 3 ^ 40 * 2129681 * 2
def baseEnd_2129681 : Nat := 1093549993747987346993281

theorem tailTrace_2129681 : CollatzResearch.WordTrace tailWord_2129681 prefixEnd_2129681 1093549993747987346993281 := by
  unfold tailWord_2129681
  simp only [CollatzResearch.WordTrace]
  refine ⟨77675847397536932402636897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51783898265024621601757931 77675847397536932402636897)
  ·
    refine ⟨58256885548152699301977673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77675847397536932402636897 58256885548152699301977673)
    ·
      refine ⟨43692664161114524476483255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58256885548152699301977673 43692664161114524476483255)
      ·
        refine ⟨65538996241671786714724883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43692664161114524476483255 65538996241671786714724883)
        ·
          refine ⟨98308494362507680072087325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65538996241671786714724883 98308494362507680072087325)
          ·
            refine ⟨36865685385940380027032747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98308494362507680072087325 36865685385940380027032747)
            ·
              refine ⟨55298528078910570040549121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36865685385940380027032747 55298528078910570040549121)
              ·
                refine ⟨41473896059182927530411841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55298528078910570040549121 41473896059182927530411841)
                ·
                  refine ⟨31105422044387195647808881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41473896059182927530411841 31105422044387195647808881)
                  ·
                    refine ⟨23329066533290396735856661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31105422044387195647808881 23329066533290396735856661)
                    ·
                      refine ⟨1093549993747987346993281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23329066533290396735856661 1093549993747987346993281)
                      ·
                        rfl

theorem cell23_2129681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_2129681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129681 prefixEnd_2129681 := by exact prefixLift 2129681
  have htrace : WordTrace (prefixWord ++ tailWord_2129681) baseStart_2129681 baseEnd_2129681 := by
    simpa [prefixWord, tailWord_2129681, baseEnd_2129681] using wordTrace_append hprefix tailTrace_2129681
  have hstable : (prefixWord ++ tailWord_2129681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129681).length < 2 ^ (prefixWord ++ tailWord_2129681).sum := by decide
  have hdescent : baseEnd_2129681 < baseStart_2129681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129682 : List Nat := [3, 2, 4, 1, 1, 2, 1, 1, 4, 4]
def baseStart_2129682 : Nat := 118140960795 + 2129682 * 2 ^ 59
def prefixEnd_2129682 : Nat := 4983230072969 + 3 ^ 40 * 2129682 * 2
def baseEnd_2129682 : Nat := 364516835742880614360259

theorem tailTrace_2129682 : CollatzResearch.WordTrace tailWord_2129682 prefixEnd_2129682 364516835742880614360259 := by
  unfold tailWord_2129682
  simp only [CollatzResearch.WordTrace]
  refine ⟨19418970967633327393355825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51783922580355539715615533 19418970967633327393355825)
  ·
    refine ⟨14564228225724995545016869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19418970967633327393355825 14564228225724995545016869)
    ·
      refine ⟨2730792792323436664690663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14564228225724995545016869 2730792792323436664690663)
      ·
        refine ⟨4096189188485154997035995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2730792792323436664690663 4096189188485154997035995)
        ·
          refine ⟨6144283782727732495553993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4096189188485154997035995 6144283782727732495553993)
          ·
            refine ⟨4608212837045799371665495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6144283782727732495553993 4608212837045799371665495)
            ·
              refine ⟨6912319255568699057498243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4608212837045799371665495 6912319255568699057498243)
              ·
                refine ⟨10368478883353048586247365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6912319255568699057498243 10368478883353048586247365)
                ·
                  refine ⟨1944089790628696609921381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10368478883353048586247365 1944089790628696609921381)
                  ·
                    refine ⟨364516835742880614360259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1944089790628696609921381 364516835742880614360259)
                    ·
                      rfl

theorem cell23_2129682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_2129682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129682 prefixEnd_2129682 := by exact prefixLift 2129682
  have htrace : WordTrace (prefixWord ++ tailWord_2129682) baseStart_2129682 baseEnd_2129682 := by
    simpa [prefixWord, tailWord_2129682, baseEnd_2129682] using wordTrace_append hprefix tailTrace_2129682
  have hstable : (prefixWord ++ tailWord_2129682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129682).length < 2 ^ (prefixWord ++ tailWord_2129682).sum := by decide
  have hdescent : baseEnd_2129682 < baseStart_2129682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129688 : List Nat := [2, 1, 2, 3, 1, 1, 2, 2, 3, 3, 3]
def baseStart_2129688 : Nat := 118140960795 + 2129688 * 2 ^ 59
def prefixEnd_2129688 : Nat := 4983230072969 + 3 ^ 40 * 2129688 * 2
def baseEnd_2129688 : Nat := 1093553588112568819605749

theorem tailTrace_2129688 : CollatzResearch.WordTrace tailWord_2129688 prefixEnd_2129688 1093553588112568819605749 := by
  unfold tailWord_2129688
  simp only [CollatzResearch.WordTrace]
  refine ⟨38838051354255786299070859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51784068472341048398761145 38838051354255786299070859)
  ·
    refine ⟨58257077031383679448606289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38838051354255786299070859 58257077031383679448606289)
    ·
      refine ⟨43692807773537759586454717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58257077031383679448606289 43692807773537759586454717)
      ·
        refine ⟨16384802915076659844920519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43692807773537759586454717 16384802915076659844920519)
        ·
          refine ⟨24577204372614989767380779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16384802915076659844920519 24577204372614989767380779)
          ·
            refine ⟨36865806558922484651071169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24577204372614989767380779 36865806558922484651071169)
            ·
              refine ⟨27649354919191863488303377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36865806558922484651071169 27649354919191863488303377)
              ·
                refine ⟨20737016189393897616227533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27649354919191863488303377 20737016189393897616227533)
                ·
                  refine ⟨7776381071022711606085325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20737016189393897616227533 7776381071022711606085325)
                  ·
                    refine ⟨2916142901633516852281997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7776381071022711606085325 2916142901633516852281997)
                    ·
                      refine ⟨1093553588112568819605749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2916142901633516852281997 1093553588112568819605749)
                      ·
                        rfl

theorem cell23_2129688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_2129688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129688 prefixEnd_2129688 := by exact prefixLift 2129688
  have htrace : WordTrace (prefixWord ++ tailWord_2129688) baseStart_2129688 baseEnd_2129688 := by
    simpa [prefixWord, tailWord_2129688, baseEnd_2129688] using wordTrace_append hprefix tailTrace_2129688
  have hstable : (prefixWord ++ tailWord_2129688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129688).length < 2 ^ (prefixWord ++ tailWord_2129688).sum := by decide
  have hdescent : baseEnd_2129688 < baseStart_2129688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129768 : List Nat := [2, 1, 4, 2, 1, 1, 2, 1, 9]
def baseStart_2129768 : Nat := 118140960795 + 2129768 * 2 ^ 59
def prefixEnd_2129768 : Nat := 4983230072969 + 3 ^ 40 * 2129768 * 2
def baseEnd_2129768 : Nat := 121510518507214278511709

theorem tailTrace_2129768 : CollatzResearch.WordTrace tailWord_2129768 prefixEnd_2129768 121510518507214278511709 := by
  unfold tailWord_2129768
  simp only [CollatzResearch.WordTrace]
  refine ⟨38839510274110873130526979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51786013698814497507369305 38839510274110873130526979)
  ·
    refine ⟨58259265411166309695790469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38839510274110873130526979 58259265411166309695790469)
    ·
      refine ⟨10923612264593683067960713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58259265411166309695790469 10923612264593683067960713)
      ·
        refine ⟨8192709198445262300970535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10923612264593683067960713 8192709198445262300970535)
        ·
          refine ⟨12289063797667893451455803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8192709198445262300970535 12289063797667893451455803)
          ·
            refine ⟨18433595696501840177183705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12289063797667893451455803 18433595696501840177183705)
            ·
              refine ⟨13825196772376380132887779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18433595696501840177183705 13825196772376380132887779)
              ·
                refine ⟨20737795158564570199331669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13825196772376380132887779 20737795158564570199331669)
                ·
                  refine ⟨121510518507214278511709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 20737795158564570199331669 121510518507214278511709)
                  ·
                    rfl

theorem cell23_2129768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 9].length) (baseStart_2129768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129768 prefixEnd_2129768 := by exact prefixLift 2129768
  have htrace : WordTrace (prefixWord ++ tailWord_2129768) baseStart_2129768 baseEnd_2129768 := by
    simpa [prefixWord, tailWord_2129768, baseEnd_2129768] using wordTrace_append hprefix tailTrace_2129768
  have hstable : (prefixWord ++ tailWord_2129768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129768).length < 2 ^ (prefixWord ++ tailWord_2129768).sum := by decide
  have hdescent : baseEnd_2129768 < baseStart_2129768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129785 : List Nat := [1, 2, 1, 3, 2, 2, 2, 5, 5]
def baseStart_2129785 : Nat := 118140960795 + 2129785 * 2 ^ 59
def prefixEnd_2129785 : Nat := 4983230072969 + 3 ^ 40 * 2129785 * 2
def baseEnd_2129785 : Nat := 121511488415117215565867

theorem tailTrace_2129785 : CollatzResearch.WordTrace tailWord_2129785 prefixEnd_2129785 121511488415117215565867 := by
  unfold tailWord_2129785
  simp only [CollatzResearch.WordTrace]
  refine ⟨77679640589160158164422809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51786427059440105442948539 77679640589160158164422809)
  ·
    refine ⟨58259730441870118623317107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77679640589160158164422809 58259730441870118623317107)
    ·
      refine ⟨87389595662805177934975661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58259730441870118623317107 87389595662805177934975661)
      ·
        refine ⟨32771098373551941725615873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87389595662805177934975661 32771098373551941725615873)
        ·
          refine ⟨24578323780163956294211905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32771098373551941725615873 24578323780163956294211905)
          ·
            refine ⟨18433742835122967220658929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24578323780163956294211905 18433742835122967220658929)
            ·
              refine ⟨13825307126342225415494197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18433742835122967220658929 13825307126342225415494197)
              ·
                refine ⟨1296122543094583632702581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13825307126342225415494197 1296122543094583632702581)
                ·
                  refine ⟨121511488415117215565867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1296122543094583632702581 121511488415117215565867)
                  ·
                    rfl

theorem cell23_2129785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 5, 5].length) (baseStart_2129785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129785 prefixEnd_2129785 := by exact prefixLift 2129785
  have htrace : WordTrace (prefixWord ++ tailWord_2129785) baseStart_2129785 baseEnd_2129785 := by
    simpa [prefixWord, tailWord_2129785, baseEnd_2129785] using wordTrace_append hprefix tailTrace_2129785
  have hstable : (prefixWord ++ tailWord_2129785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129785).length < 2 ^ (prefixWord ++ tailWord_2129785).sum := by decide
  have hdescent : baseEnd_2129785 < baseStart_2129785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129812 : List Nat := [2, 4, 2, 1, 1, 3, 1, 1, 2, 3, 3]
def baseStart_2129812 : Nat := 118140960795 + 2129812 * 2 ^ 59
def prefixEnd_2129812 : Nat := 4983230072969 + 3 ^ 40 * 2129812 * 2
def baseEnd_2129812 : Nat := 1093617259713726334455179

theorem tailTrace_2129812 : CollatzResearch.WordTrace tailWord_2129812 prefixEnd_2129812 1093617259713726334455179 := by
  unfold tailWord_2129812
  simp only [CollatzResearch.WordTrace]
  refine ⟨38840312680031170887827845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51787083573374894517103793 38840312680031170887827845)
  ·
    refine ⟨7282558627505844541467721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38840312680031170887827845 7282558627505844541467721)
    ·
      refine ⟨5461918970629383406100791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7282558627505844541467721 5461918970629383406100791)
      ·
        refine ⟨8192878455944075109151187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5461918970629383406100791 8192878455944075109151187)
        ·
          refine ⟨12289317683916112663726781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8192878455944075109151187 12289317683916112663726781)
          ·
            refine ⟨4608494131468542248897543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12289317683916112663726781 4608494131468542248897543)
            ·
              refine ⟨6912741197202813373346315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4608494131468542248897543 6912741197202813373346315)
              ·
                refine ⟨10369111795804220060019473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6912741197202813373346315 10369111795804220060019473)
                ·
                  refine ⟨7776833846853165045014605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10369111795804220060019473 7776833846853165045014605)
                  ·
                    refine ⟨2916312692569936891880477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7776833846853165045014605 2916312692569936891880477)
                    ·
                      refine ⟨1093617259713726334455179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2916312692569936891880477 1093617259713726334455179)
                      ·
                        rfl

theorem cell23_2129812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_2129812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129812 prefixEnd_2129812 := by exact prefixLift 2129812
  have htrace : WordTrace (prefixWord ++ tailWord_2129812) baseStart_2129812 baseEnd_2129812 := by
    simpa [prefixWord, tailWord_2129812, baseEnd_2129812] using wordTrace_append hprefix tailTrace_2129812
  have hstable : (prefixWord ++ tailWord_2129812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129812).length < 2 ^ (prefixWord ++ tailWord_2129812).sum := by decide
  have hdescent : baseEnd_2129812 < baseStart_2129812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129835 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 6, 4, 2]
def baseStart_2129835 : Nat := 118140960795 + 2129835 * 2 ^ 59
def prefixEnd_2129835 : Nat := 4983230072969 + 3 ^ 40 * 2129835 * 2
def baseEnd_2129835 : Nat := 1093629069768779744467573

theorem tailTrace_2129835 : CollatzResearch.WordTrace tailWord_2129835 prefixEnd_2129835 1093629069768779744467573 := by
  unfold tailWord_2129835
  simp only [CollatzResearch.WordTrace]
  refine ⟨77681464238979016703742959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51787642825986011135828639 77681464238979016703742959)
  ·
    refine ⟨116522196358468525055614439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77681464238979016703742959 116522196358468525055614439)
    ·
      refine ⟨174783294537702787583421659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116522196358468525055614439 174783294537702787583421659)
      ·
        refine ⟨262174941806554181375132489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174783294537702787583421659 262174941806554181375132489)
        ·
          refine ⟨196631206354915636031349367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 262174941806554181375132489 196631206354915636031349367)
          ·
            refine ⟨294946809532373454047024051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196631206354915636031349367 294946809532373454047024051)
            ·
              refine ⟨442420214298560181070536077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 294946809532373454047024051 442420214298560181070536077)
              ·
                refine ⟨165907580361960067901451029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 442420214298560181070536077 165907580361960067901451029)
                ·
                  refine ⟨7776917829466878182880517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 165907580361960067901451029 7776917829466878182880517)
                  ·
                    refine ⟨1458172093025039659290097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7776917829466878182880517 1458172093025039659290097)
                    ·
                      refine ⟨1093629069768779744467573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1458172093025039659290097 1093629069768779744467573)
                      ·
                        rfl

theorem cell23_2129835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 4, 2].length) (baseStart_2129835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129835 prefixEnd_2129835 := by exact prefixLift 2129835
  have htrace : WordTrace (prefixWord ++ tailWord_2129835) baseStart_2129835 baseEnd_2129835 := by
    simpa [prefixWord, tailWord_2129835, baseEnd_2129835] using wordTrace_append hprefix tailTrace_2129835
  have hstable : (prefixWord ++ tailWord_2129835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129835).length < 2 ^ (prefixWord ++ tailWord_2129835).sum := by decide
  have hdescent : baseEnd_2129835 < baseStart_2129835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129848 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 1, 3, 6]
def baseStart_2129848 : Nat := 118140960795 + 2129848 * 2 ^ 59
def prefixEnd_2129848 : Nat := 4983230072969 + 3 ^ 40 * 2129848 * 2
def baseEnd_2129848 : Nat := 1093635745017288193605013

theorem tailTrace_2129848 : CollatzResearch.WordTrace tailWord_2129848 prefixEnd_2129848 1093635745017288193605013 := by
  unfold tailWord_2129848
  simp only [CollatzResearch.WordTrace]
  refine ⟨38840969193965959961983099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51787958925287946615977465 38840969193965959961983099)
  ·
    refine ⟨58261453790948939942974649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38840969193965959961983099 58261453790948939942974649)
    ·
      refine ⟨43696090343211704957230987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58261453790948939942974649 43696090343211704957230987)
      ·
        refine ⟨65544135514817557435846481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43696090343211704957230987 65544135514817557435846481)
        ·
          refine ⟨49158101636113168076884861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65544135514817557435846481 49158101636113168076884861)
          ·
            refine ⟨18434288113542438028831823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49158101636113168076884861 18434288113542438028831823)
            ·
              refine ⟨27651432170313657043247735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18434288113542438028831823 27651432170313657043247735)
              ·
                refine ⟨41477148255470485564871603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27651432170313657043247735 41477148255470485564871603)
                ·
                  refine ⟨62215722383205728347307405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41477148255470485564871603 62215722383205728347307405)
                  ·
                    refine ⟨23330895893702148130240277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62215722383205728347307405 23330895893702148130240277)
                    ·
                      refine ⟨1093635745017288193605013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23330895893702148130240277 1093635745017288193605013)
                      ·
                        rfl

theorem cell23_2129848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_2129848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129848 prefixEnd_2129848 := by exact prefixLift 2129848
  have htrace : WordTrace (prefixWord ++ tailWord_2129848) baseStart_2129848 baseEnd_2129848 := by
    simpa [prefixWord, tailWord_2129848, baseEnd_2129848] using wordTrace_append hprefix tailTrace_2129848
  have hstable : (prefixWord ++ tailWord_2129848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129848).length < 2 ^ (prefixWord ++ tailWord_2129848).sum := by decide
  have hdescent : baseEnd_2129848 < baseStart_2129848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129855 : List Nat := [1, 1, 2, 2, 2, 1, 4, 1, 4, 2, 3]
def baseStart_2129855 : Nat := 118140960795 + 2129855 * 2 ^ 59
def prefixEnd_2129855 : Nat := 4983230072969 + 3 ^ 40 * 2129855 * 2
def baseEnd_2129855 : Nat := 1093639339381869666217481

theorem tailTrace_2129855 : CollatzResearch.WordTrace tailWord_2129855 prefixEnd_2129855 1093639339381869666217481 := by
  unfold tailWord_2129855
  simp only [CollatzResearch.WordTrace]
  refine ⟨77682193698906560119471019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51788129132604373412980679 77682193698906560119471019)
  ·
    refine ⟨116523290548359840179206529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77682193698906560119471019 116523290548359840179206529)
    ·
      refine ⟨87392467911269880134404897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116523290548359840179206529 87392467911269880134404897)
      ·
        refine ⟨65544350933452410100803673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87392467911269880134404897 65544350933452410100803673)
        ·
          refine ⟨49158263200089307575602755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65544350933452410100803673 49158263200089307575602755)
          ·
            refine ⟨73737394800133961363404133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49158263200089307575602755 73737394800133961363404133)
            ·
              refine ⟨13825761525025117755638275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73737394800133961363404133 13825761525025117755638275)
              ·
                refine ⟨20738642287537676633457413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13825761525025117755638275 20738642287537676633457413)
                ·
                  refine ⟨3888495428913314368773265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20738642287537676633457413 3888495428913314368773265)
                  ·
                    refine ⟨2916371571684985776579949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3888495428913314368773265 2916371571684985776579949)
                    ·
                      refine ⟨1093639339381869666217481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2916371571684985776579949 1093639339381869666217481)
                      ·
                        rfl

theorem cell23_2129855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 4, 2, 3].length) (baseStart_2129855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129855 prefixEnd_2129855 := by exact prefixLift 2129855
  have htrace : WordTrace (prefixWord ++ tailWord_2129855) baseStart_2129855 baseEnd_2129855 := by
    simpa [prefixWord, tailWord_2129855, baseEnd_2129855] using wordTrace_append hprefix tailTrace_2129855
  have hstable : (prefixWord ++ tailWord_2129855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129855).length < 2 ^ (prefixWord ++ tailWord_2129855).sum := by decide
  have hdescent : baseEnd_2129855 < baseStart_2129855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129888 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 2, 9]
def baseStart_2129888 : Nat := 118140960795 + 2129888 * 2 ^ 59
def prefixEnd_2129888 : Nat := 4983230072969 + 3 ^ 40 * 2129888 * 2
def baseEnd_2129888 : Nat := 364552094747822679034943

theorem tailTrace_2129888 : CollatzResearch.WordTrace tailWord_2129888 prefixEnd_2129888 364552094747822679034943 := by
  unfold tailWord_2129888
  simp only [CollatzResearch.WordTrace]
  refine ⟨38841698653893503377711159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51788931538524671170281545 38841698653893503377711159)
  ·
    refine ⟨58262547980840255066566739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38841698653893503377711159 58262547980840255066566739)
    ·
      refine ⟨87393821971260382599850109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58262547980840255066566739 87393821971260382599850109)
      ·
        refine ⟨32772683239222643474943791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87393821971260382599850109 32772683239222643474943791)
        ·
          refine ⟨49159024858833965212415687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32772683239222643474943791 49159024858833965212415687)
          ·
            refine ⟨73738537288250947818623531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49159024858833965212415687 73738537288250947818623531)
            ·
              refine ⟨110607805932376421727935297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73738537288250947818623531 110607805932376421727935297)
              ·
                refine ⟨82955854449282316295951473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110607805932376421727935297 82955854449282316295951473)
                ·
                  refine ⟨62216890836961737221963605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82955854449282316295951473 62216890836961737221963605)
                  ·
                    refine ⟨364552094747822679034943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 62216890836961737221963605 364552094747822679034943)
                    ·
                      rfl

theorem cell23_2129888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 2, 9].length) (baseStart_2129888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129888 prefixEnd_2129888 := by exact prefixLift 2129888
  have htrace : WordTrace (prefixWord ++ tailWord_2129888) baseStart_2129888 baseEnd_2129888 := by
    simpa [prefixWord, tailWord_2129888, baseEnd_2129888] using wordTrace_append hprefix tailTrace_2129888
  have hstable : (prefixWord ++ tailWord_2129888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129888).length < 2 ^ (prefixWord ++ tailWord_2129888).sum := by decide
  have hdescent : baseEnd_2129888 < baseStart_2129888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129912 : List Nat := [2, 1, 2, 1, 1, 3, 3, 1, 4, 3, 2]
def baseStart_2129912 : Nat := 118140960795 + 2129912 * 2 ^ 59
def prefixEnd_2129912 : Nat := 4983230072969 + 3 ^ 40 * 2129912 * 2
def baseEnd_2129912 : Nat := 1093668607779175943204719

theorem tailTrace_2129912 : CollatzResearch.WordTrace tailWord_2129912 prefixEnd_2129912 1093668607779175943204719 := by
  unfold tailWord_2129912
  simp only [CollatzResearch.WordTrace]
  refine ⟨38842136329850029427147995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51789515106466705902863993 38842136329850029427147995)
  ·
    refine ⟨58263204494775044140721993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38842136329850029427147995 58263204494775044140721993)
    ·
      refine ⟨43697403371081283105541495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58263204494775044140721993 43697403371081283105541495)
      ·
        refine ⟨65546105056621924658312243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43697403371081283105541495 65546105056621924658312243)
        ·
          refine ⟨98319157584932886987468365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65546105056621924658312243 98319157584932886987468365)
          ·
            refine ⟨36869684094349832620300637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98319157584932886987468365 36869684094349832620300637)
            ·
              refine ⟨13826131535381187232612739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36869684094349832620300637 13826131535381187232612739)
              ·
                refine ⟨20739197303071780848919109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13826131535381187232612739 20739197303071780848919109)
                ·
                  refine ⟨3888599494325958909172333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20739197303071780848919109 3888599494325958909172333)
                  ·
                    refine ⟨1458224810372234590939625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3888599494325958909172333 1458224810372234590939625)
                    ·
                      refine ⟨1093668607779175943204719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1458224810372234590939625 1093668607779175943204719)
                      ·
                        rfl

theorem cell23_2129912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 4, 3, 2].length) (baseStart_2129912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129912 prefixEnd_2129912 := by exact prefixLift 2129912
  have htrace : WordTrace (prefixWord ++ tailWord_2129912) baseStart_2129912 baseEnd_2129912 := by
    simpa [prefixWord, tailWord_2129912, baseEnd_2129912] using wordTrace_append hprefix tailTrace_2129912
  have hstable : (prefixWord ++ tailWord_2129912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129912).length < 2 ^ (prefixWord ++ tailWord_2129912).sum := by decide
  have hdescent : baseEnd_2129912 < baseStart_2129912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129919 : List Nat := [1, 1, 2, 2, 1, 2, 1, 8, 1, 1, 3]
def baseStart_2129919 : Nat := 118140960795 + 2129919 * 2 ^ 59
def prefixEnd_2129919 : Nat := 4983230072969 + 3 ^ 40 * 2129919 * 2
def baseEnd_2129919 : Nat := 1093672202143757415817187

theorem tailTrace_2129919 : CollatzResearch.WordTrace tailWord_2129919 prefixEnd_2129919 1093672202143757415817187 := by
  unfold tailWord_2129919
  simp only [CollatzResearch.WordTrace]
  refine ⟨77684527970674699049800811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51789685313783132699867207 77684527970674699049800811)
  ·
    refine ⟨116526791956012048574701217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77684527970674699049800811 116526791956012048574701217)
    ·
      refine ⟨87395093967009036431025913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116526791956012048574701217 87395093967009036431025913)
      ·
        refine ⟨65546320475256777323269435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87395093967009036431025913 65546320475256777323269435)
        ·
          refine ⟨98319480712885165984904153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65546320475256777323269435 98319480712885165984904153)
          ·
            refine ⟨73739610534663874488678115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98319480712885165984904153 73739610534663874488678115)
            ·
              refine ⟨110609415801995811733017173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73739610534663874488678115 110609415801995811733017173)
              ·
                refine ⟨1296204091429638418746295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 110609415801995811733017173 1296204091429638418746295)
                ·
                  refine ⟨1944306137144457628119443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1296204091429638418746295 1944306137144457628119443)
                  ·
                    refine ⟨2916459205716686442179165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1944306137144457628119443 2916459205716686442179165)
                    ·
                      refine ⟨1093672202143757415817187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2916459205716686442179165 1093672202143757415817187)
                      ·
                        rfl

theorem cell23_2129919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 8, 1, 1, 3].length) (baseStart_2129919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129919 prefixEnd_2129919 := by exact prefixLift 2129919
  have htrace : WordTrace (prefixWord ++ tailWord_2129919) baseStart_2129919 baseEnd_2129919 := by
    simpa [prefixWord, tailWord_2129919, baseEnd_2129919] using wordTrace_append hprefix tailTrace_2129919
  have hstable : (prefixWord ++ tailWord_2129919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129919).length < 2 ^ (prefixWord ++ tailWord_2129919).sum := by decide
  have hdescent : baseEnd_2129919 < baseStart_2129919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129956 : List Nat := [2, 3, 1, 4, 2, 1, 3, 1, 1, 5]
def baseStart_2129956 : Nat := 118140960795 + 2129956 * 2 ^ 59
def prefixEnd_2129956 : Nat := 4983230072969 + 3 ^ 40 * 2129956 * 2
def baseEnd_2129956 : Nat := 364563733642657923684839

theorem tailTrace_2129956 : CollatzResearch.WordTrace tailWord_2129956 prefixEnd_2129956 364563733642657923684839 := by
  unfold tailWord_2129956
  simp only [CollatzResearch.WordTrace]
  refine ⟨38842938735770327184448861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51790584981027102912598481 38842938735770327184448861)
  ·
    refine ⟨14566102025913872694168323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38842938735770327184448861 14566102025913872694168323)
    ·
      refine ⟨21849153038870809041252485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14566102025913872694168323 21849153038870809041252485)
      ·
        refine ⟨4096716194788276695234841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21849153038870809041252485 4096716194788276695234841)
        ·
          refine ⟨3072537146091207521426131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4096716194788276695234841 3072537146091207521426131)
          ·
            refine ⟨4608805719136811282139197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3072537146091207521426131 4608805719136811282139197)
            ·
              refine ⟨1728302144676304230802199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4608805719136811282139197 1728302144676304230802199)
              ·
                refine ⟨2592453217014456346203299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1728302144676304230802199 2592453217014456346203299)
                ·
                  refine ⟨3888679825521684519304949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2592453217014456346203299 3888679825521684519304949)
                  ·
                    refine ⟨364563733642657923684839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3888679825521684519304949 364563733642657923684839)
                    ·
                      rfl

theorem cell23_2129956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 1, 1, 5].length) (baseStart_2129956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129956 prefixEnd_2129956 := by exact prefixLift 2129956
  have htrace : WordTrace (prefixWord ++ tailWord_2129956) baseStart_2129956 baseEnd_2129956 := by
    simpa [prefixWord, tailWord_2129956, baseEnd_2129956] using wordTrace_append hprefix tailTrace_2129956
  have hstable : (prefixWord ++ tailWord_2129956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129956).length < 2 ^ (prefixWord ++ tailWord_2129956).sum := by decide
  have hdescent : baseEnd_2129956 < baseStart_2129956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129969 : List Nat := [1, 2, 2, 3, 1, 4, 2, 2, 2, 4]
def baseStart_2129969 : Nat := 118140960795 + 2129969 * 2 ^ 59
def prefixEnd_2129969 : Nat := 4983230072969 + 3 ^ 40 * 2129969 * 2
def baseEnd_2129969 : Nat := 364565958725494073397319

theorem tailTrace_2129969 : CollatzResearch.WordTrace tailWord_2129969 prefixEnd_2129969 364565958725494073397319 := by
  unfold tailWord_2129969
  simp only [CollatzResearch.WordTrace]
  refine ⟨77686351620493557589120961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51790901080329038392747307 77686351620493557589120961)
  ·
    refine ⟨58264763715370168191840721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77686351620493557589120961 58264763715370168191840721)
    ·
      refine ⟨43698572786527626143880541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58264763715370168191840721 43698572786527626143880541)
      ·
        refine ⟨16386964794947859803955203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43698572786527626143880541 16386964794947859803955203)
        ·
          refine ⟨24580447192421789705932805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16386964794947859803955203 24580447192421789705932805)
          ·
            refine ⟨4608833848579085569862401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24580447192421789705932805 4608833848579085569862401)
            ·
              refine ⟨3456625386434314177396801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4608833848579085569862401 3456625386434314177396801)
              ·
                refine ⟨2592469039825735633047601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3456625386434314177396801 2592469039825735633047601)
                ·
                  refine ⟨1944351779869301724785701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2592469039825735633047601 1944351779869301724785701)
                  ·
                    refine ⟨364565958725494073397319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1944351779869301724785701 364565958725494073397319)
                    ·
                      rfl

theorem cell23_2129969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 2, 2, 4].length) (baseStart_2129969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129969 prefixEnd_2129969 := by exact prefixLift 2129969
  have htrace : WordTrace (prefixWord ++ tailWord_2129969) baseStart_2129969 baseEnd_2129969 := by
    simpa [prefixWord, tailWord_2129969, baseEnd_2129969] using wordTrace_append hprefix tailTrace_2129969
  have hstable : (prefixWord ++ tailWord_2129969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129969).length < 2 ^ (prefixWord ++ tailWord_2129969).sum := by decide
  have hdescent : baseEnd_2129969 < baseStart_2129969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130006 : List Nat := [5, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4]
def baseStart_2130006 : Nat := 118140960795 + 2130006 * 2 ^ 59
def prefixEnd_2130006 : Nat := 4983230072969 + 3 ^ 40 * 2130006 * 2
def baseEnd_2130006 : Nat := 1093716874960698575429287

theorem tailTrace_2130006 : CollatzResearch.WordTrace tailWord_2130006 prefixEnd_2130006 1093716874960698575429287 := by
  unfold tailWord_2130006
  simp only [CollatzResearch.WordTrace]
  refine ⟨4855481320084969556763617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51791800747573008605478581 4855481320084969556763617)
  ·
    refine ⟨3641610990063727167572713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4855481320084969556763617 3641610990063727167572713)
    ·
      refine ⟨2731208242547795375679535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3641610990063727167572713 2731208242547795375679535)
      ·
        refine ⟨4096812363821693063519303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2731208242547795375679535 4096812363821693063519303)
        ·
          refine ⟨6145218545732539595278955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4096812363821693063519303 6145218545732539595278955)
          ·
            refine ⟨9217827818598809392918433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6145218545732539595278955 9217827818598809392918433)
            ·
              refine ⟨6913370863949107044688825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9217827818598809392918433 6913370863949107044688825)
              ·
                refine ⟨5185028147961830283516619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6913370863949107044688825 5185028147961830283516619)
                ·
                  refine ⟨7777542221942745425274929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5185028147961830283516619 7777542221942745425274929)
                  ·
                    refine ⟨5833156666457059068956197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7777542221942745425274929 5833156666457059068956197)
                    ·
                      refine ⟨1093716874960698575429287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5833156666457059068956197 1093716874960698575429287)
                      ·
                        rfl

theorem cell23_2130006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_2130006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2130006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2130006 prefixEnd_2130006 := by exact prefixLift 2130006
  have htrace : WordTrace (prefixWord ++ tailWord_2130006) baseStart_2130006 baseEnd_2130006 := by
    simpa [prefixWord, tailWord_2130006, baseEnd_2130006] using wordTrace_append hprefix tailTrace_2130006
  have hstable : (prefixWord ++ tailWord_2130006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130006).length < 2 ^ (prefixWord ++ tailWord_2130006).sum := by decide
  have hdescent : baseEnd_2130006 < baseStart_2130006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130013 : List Nat := [1, 4, 4, 1, 1, 1, 4, 1, 1, 2, 3]
def baseStart_2130013 : Nat := 118140960795 + 2130013 * 2 ^ 59
def prefixEnd_2130013 : Nat := 4983230072969 + 3 ^ 40 * 2130013 * 2
def baseEnd_2130013 : Nat := 1093720469325280048041755

theorem tailTrace_2130013 : CollatzResearch.WordTrace tailWord_2130013 prefixEnd_2130013 1093720469325280048041755 := by
  unfold tailWord_2130013
  simp only [CollatzResearch.WordTrace]
  refine ⟨77687956432334153103722693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51791970954889435402481795 77687956432334153103722693)
  ·
    refine ⟨14566491831062653706948005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77687956432334153103722693 14566491831062653706948005)
    ·
      refine ⟨2731217218324247570052751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14566491831062653706948005 2731217218324247570052751)
      ·
        refine ⟨4096825827486371355079127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2731217218324247570052751 4096825827486371355079127)
        ·
          refine ⟨6145238741229557032618691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4096825827486371355079127 6145238741229557032618691)
          ·
            refine ⟨9217858111844335548928037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6145238741229557032618691 9217858111844335548928037)
            ·
              refine ⟨1728348395970812915424007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9217858111844335548928037 1728348395970812915424007)
              ·
                refine ⟨2592522593956219373136011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1728348395970812915424007 2592522593956219373136011)
                ·
                  refine ⟨3888783890934329059704017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2592522593956219373136011 3888783890934329059704017)
                  ·
                    refine ⟨2916587918200746794778013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3888783890934329059704017 2916587918200746794778013)
                    ·
                      refine ⟨1093720469325280048041755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2916587918200746794778013 1093720469325280048041755)
                      ·
                        rfl

theorem cell23_2130013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_2130013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2130013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2130013 prefixEnd_2130013 := by exact prefixLift 2130013
  have htrace : WordTrace (prefixWord ++ tailWord_2130013) baseStart_2130013 baseEnd_2130013 := by
    simpa [prefixWord, tailWord_2130013, baseEnd_2130013] using wordTrace_append hprefix tailTrace_2130013
  have hstable : (prefixWord ++ tailWord_2130013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130013).length < 2 ^ (prefixWord ++ tailWord_2130013).sum := by decide
  have hdescent : baseEnd_2130013 < baseStart_2130013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130015 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 1, 5, 4]
def baseStart_2130015 : Nat := 118140960795 + 2130015 * 2 ^ 59
def prefixEnd_2130015 : Nat := 4983230072969 + 3 ^ 40 * 2130015 * 2
def baseEnd_2130015 : Nat := 1093721496286589040216745

theorem tailTrace_2130015 : CollatzResearch.WordTrace tailWord_2130015 prefixEnd_2130015 1093721496286589040216745 := by
  unfold tailWord_2130015
  simp only [CollatzResearch.WordTrace]
  refine ⟨77688029378326907445295499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51792019585551271630196999 77688029378326907445295499)
  ·
    refine ⟨116532044067490361167943249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77688029378326907445295499 116532044067490361167943249)
    ·
      refine ⟨87399033050617770875957437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116532044067490361167943249 87399033050617770875957437)
      ·
        refine ⟨32774637393981664078484039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87399033050617770875957437 32774637393981664078484039)
        ·
          refine ⟨49161956090972496117726059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32774637393981664078484039 49161956090972496117726059)
          ·
            refine ⟨73742934136458744176589089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49161956090972496117726059 73742934136458744176589089)
            ·
              refine ⟨55307200602344058132441817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73742934136458744176589089 55307200602344058132441817)
              ·
                refine ⟨41480400451758043599331363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55307200602344058132441817 41480400451758043599331363)
                ·
                  refine ⟨62220600677637065398997045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41480400451758043599331363 62220600677637065398997045)
                  ·
                    refine ⟨5833181313528474881155973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 62220600677637065398997045 5833181313528474881155973)
                    ·
                      refine ⟨1093721496286589040216745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5833181313528474881155973 1093721496286589040216745)
                      ·
                        rfl

theorem cell23_2130015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_2130015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2130015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2130015 prefixEnd_2130015 := by exact prefixLift 2130015
  have htrace : WordTrace (prefixWord ++ tailWord_2130015) baseStart_2130015 baseEnd_2130015 := by
    simpa [prefixWord, tailWord_2130015, baseEnd_2130015] using wordTrace_append hprefix tailTrace_2130015
  have hstable : (prefixWord ++ tailWord_2130015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130015).length < 2 ^ (prefixWord ++ tailWord_2130015).sum := by decide
  have hdescent : baseEnd_2130015 < baseStart_2130015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130025 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 4, 6]
def baseStart_2130025 : Nat := 118140960795 + 2130025 * 2 ^ 59
def prefixEnd_2130025 : Nat := 4983230072969 + 3 ^ 40 * 2130025 * 2
def baseEnd_2130025 : Nat := 364575543697711333697233

theorem tailTrace_2130025 : CollatzResearch.WordTrace tailWord_2130025 prefixEnd_2130025 364575543697711333697233 := by
  unfold tailWord_2130025
  simp only [CollatzResearch.WordTrace]
  refine ⟨77688394108290679153159529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51792262738860452768773019 77688394108290679153159529)
  ·
    refine ⟨58266295581218009364869647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77688394108290679153159529 58266295581218009364869647)
    ·
      refine ⟨87399443371827014047304471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58266295581218009364869647 87399443371827014047304471)
      ·
        refine ⟨131099165057740521070956707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87399443371827014047304471 131099165057740521070956707)
        ·
          refine ⟨196648747586610781606435061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131099165057740521070956707 196648747586610781606435061)
          ·
            refine ⟨18435820086244760775603287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 196648747586610781606435061 18435820086244760775603287)
            ·
              refine ⟨27653730129367141163404931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18435820086244760775603287 27653730129367141163404931)
              ·
                refine ⟨41480595194050711745107397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27653730129367141163404931 41480595194050711745107397)
                ·
                  refine ⟨7777611598884508452207637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41480595194050711745107397 7777611598884508452207637)
                  ·
                    refine ⟨364575543697711333697233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7777611598884508452207637 364575543697711333697233)
                    ·
                      rfl

theorem cell23_2130025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 6].length) (baseStart_2130025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2130025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2130025 prefixEnd_2130025 := by exact prefixLift 2130025
  have htrace : WordTrace (prefixWord ++ tailWord_2130025) baseStart_2130025 baseEnd_2130025 := by
    simpa [prefixWord, tailWord_2130025, baseEnd_2130025] using wordTrace_append hprefix tailTrace_2130025
  have hstable : (prefixWord ++ tailWord_2130025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130025).length < 2 ^ (prefixWord ++ tailWord_2130025).sum := by decide
  have hdescent : baseEnd_2130025 < baseStart_2130025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130026 : List Nat := [3, 1, 3, 2, 3, 1, 1, 1, 4, 1, 3]
def baseStart_2130026 : Nat := 118140960795 + 2130026 * 2 ^ 59
def prefixEnd_2130026 : Nat := 4983230072969 + 3 ^ 40 * 2130026 * 2
def baseEnd_2130026 : Nat := 1093727144573788497179195

theorem tailTrace_2130026 : CollatzResearch.WordTrace tailWord_2130026 prefixEnd_2130026 1093727144573788497179195 := by
  unfold tailWord_2130026
  simp only [CollatzResearch.WordTrace]
  refine ⟨19422107645321764080986483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51792287054191370882630621 19422107645321764080986483)
  ·
    refine ⟨29133161467982646121479725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19422107645321764080986483 29133161467982646121479725)
    ·
      refine ⟨10924935550493492295554897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29133161467982646121479725 10924935550493492295554897)
      ·
        refine ⟨8193701662870119221666173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10924935550493492295554897 8193701662870119221666173)
        ·
          refine ⟨3072638123576294708124815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8193701662870119221666173 3072638123576294708124815)
          ·
            refine ⟨4608957185364442062187223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3072638123576294708124815 4608957185364442062187223)
            ·
              refine ⟨6913435778046663093280835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4608957185364442062187223 6913435778046663093280835)
              ·
                refine ⟨10370153667069994639921253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6913435778046663093280835 10370153667069994639921253)
                ·
                  refine ⟨1944403812575623994985235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10370153667069994639921253 1944403812575623994985235)
                  ·
                    refine ⟨2916605718863435992477853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1944403812575623994985235 2916605718863435992477853)
                    ·
                      refine ⟨1093727144573788497179195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2916605718863435992477853 1093727144573788497179195)
                      ·
                        rfl

theorem cell23_2130026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_2130026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2130026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2130026 prefixEnd_2130026 := by exact prefixLift 2130026
  have htrace : WordTrace (prefixWord ++ tailWord_2130026) baseStart_2130026 baseEnd_2130026 := by
    simpa [prefixWord, tailWord_2130026, baseEnd_2130026] using wordTrace_append hprefix tailTrace_2130026
  have hstable : (prefixWord ++ tailWord_2130026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130026).length < 2 ^ (prefixWord ++ tailWord_2130026).sum := by decide
  have hdescent : baseEnd_2130026 < baseStart_2130026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130052 : List Nat := [2, 3, 2, 1, 2, 1, 2, 2, 2, 1, 5]
def baseStart_2130052 : Nat := 118140960795 + 2130052 * 2 ^ 59
def prefixEnd_2130052 : Nat := 4983230072969 + 3 ^ 40 * 2130052 * 2
def baseEnd_2130052 : Nat := 1093740495070805395454075

theorem tailTrace_2130052 : CollatzResearch.WordTrace tailWord_2130052 prefixEnd_2130052 1093740495070805395454075 := by
  unfold tailWord_2130052
  simp only [CollatzResearch.WordTrace]
  refine ⟨38844689439596431382196205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51792919252795241842928273 38844689439596431382196205)
  ·
    refine ⟨14566758539848661768323577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38844689439596431382196205 14566758539848661768323577)
    ·
      refine ⟨10925068904886496326242683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14566758539848661768323577 10925068904886496326242683)
      ·
        refine ⟨16387603357329744489364025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10925068904886496326242683 16387603357329744489364025)
        ·
          refine ⟨12290702517997308367023019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16387603357329744489364025 12290702517997308367023019)
          ·
            refine ⟨18436053776995962550534529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12290702517997308367023019 18436053776995962550534529)
            ·
              refine ⟨13827040332746971912900897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18436053776995962550534529 13827040332746971912900897)
              ·
                refine ⟨10370280249560228934675673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13827040332746971912900897 10370280249560228934675673)
                ·
                  refine ⟨7777710187170171701006755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10370280249560228934675673 7777710187170171701006755)
                  ·
                    refine ⟨11666565280755257551510133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7777710187170171701006755 11666565280755257551510133)
                    ·
                      refine ⟨1093740495070805395454075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11666565280755257551510133 1093740495070805395454075)
                      ·
                        rfl

theorem cell23_2130052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_2130052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2130052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2130052 prefixEnd_2130052 := by exact prefixLift 2130052
  have htrace : WordTrace (prefixWord ++ tailWord_2130052) baseStart_2130052 baseEnd_2130052 := by
    simpa [prefixWord, tailWord_2130052, baseEnd_2130052] using wordTrace_append hprefix tailTrace_2130052
  have hstable : (prefixWord ++ tailWord_2130052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130052).length < 2 ^ (prefixWord ++ tailWord_2130052).sum := by decide
  have hdescent : baseEnd_2130052 < baseStart_2130052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130066 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 6, 2, 2]
def baseStart_2130066 : Nat := 118140960795 + 2130066 * 2 ^ 59
def prefixEnd_2130066 : Nat := 4983230072969 + 3 ^ 40 * 2130066 * 2
def baseEnd_2130066 : Nat := 1093747683799968340679011

theorem tailTrace_2130066 : CollatzResearch.WordTrace tailWord_2130066 prefixEnd_2130066 1093747683799968340679011 := by
  unfold tailWord_2130066
  simp only [CollatzResearch.WordTrace]
  refine ⟨19422472375285535788850513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51793259667428095436934701 19422472375285535788850513)
  ·
    refine ⟨14566854281464151841637885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19422472375285535788850513 14566854281464151841637885)
    ·
      refine ⟨5462570355549056940614207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14566854281464151841637885 5462570355549056940614207)
      ·
        refine ⟨8193855533323585410921311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5462570355549056940614207 8193855533323585410921311)
        ·
          refine ⟨12290783299985378116381967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8193855533323585410921311 12290783299985378116381967)
          ·
            refine ⟨18436174949978067174572951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12290783299985378116381967 18436174949978067174572951)
            ·
              refine ⟨27654262424967100761859427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18436174949978067174572951 27654262424967100761859427)
              ·
                refine ⟨41481393637450651142789141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27654262424967100761859427 41481393637450651142789141)
                ·
                  refine ⟨1944440326755499272318241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 41481393637450651142789141 1944440326755499272318241)
                  ·
                    refine ⟨1458330245066624454238681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1944440326755499272318241 1458330245066624454238681)
                    ·
                      refine ⟨1093747683799968340679011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1458330245066624454238681 1093747683799968340679011)
                      ·
                        rfl

theorem cell23_2130066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_2130066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2130066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2130066 prefixEnd_2130066 := by exact prefixLift 2130066
  have htrace : WordTrace (prefixWord ++ tailWord_2130066) baseStart_2130066 baseEnd_2130066 := by
    simpa [prefixWord, tailWord_2130066, baseEnd_2130066] using wordTrace_append hprefix tailTrace_2130066
  have hstable : (prefixWord ++ tailWord_2130066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130066).length < 2 ^ (prefixWord ++ tailWord_2130066).sum := by decide
  have hdescent : baseEnd_2130066 < baseStart_2130066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130094 : List Nat := [4, 1, 4, 2, 2, 1, 2, 1, 2, 1, 3]
def baseStart_2130094 : Nat := 118140960795 + 2130094 * 2 ^ 59
def prefixEnd_2130094 : Nat := 4983230072969 + 3 ^ 40 * 2130094 * 2
def baseEnd_2130094 : Nat := 1093762061258294231128883

theorem tailTrace_2130094 : CollatzResearch.WordTrace tailWord_2130094 prefixEnd_2130094 1093762061258294231128883 := by
  unfold tailWord_2130094
  simp only [CollatzResearch.WordTrace]
  refine ⟨9711363843130087992177667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51793940496693802624947557 9711363843130087992177667)
  ·
    refine ⟨14567045764695131988266501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9711363843130087992177667 14567045764695131988266501)
    ·
      refine ⟨2731321080880337247799969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14567045764695131988266501 2731321080880337247799969)
      ·
        refine ⟨2048490810660252935849977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2731321080880337247799969 2048490810660252935849977)
        ·
          refine ⟨1536368107995189701887483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2048490810660252935849977 1536368107995189701887483)
          ·
            refine ⟨2304552161992784552831225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1536368107995189701887483 2304552161992784552831225)
            ·
              refine ⟨1728414121494588414623419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2304552161992784552831225 1728414121494588414623419)
              ·
                refine ⟨2592621182241882621935129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1728414121494588414623419 2592621182241882621935129)
                ·
                  refine ⟨1944465886681411966451347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2592621182241882621935129 1944465886681411966451347)
                  ·
                    refine ⟨2916698830022117949677021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1944465886681411966451347 2916698830022117949677021)
                    ·
                      refine ⟨1093762061258294231128883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2916698830022117949677021 1093762061258294231128883)
                      ·
                        rfl

theorem cell23_2130094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_2130094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2130094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2130094 prefixEnd_2130094 := by exact prefixLift 2130094
  have htrace : WordTrace (prefixWord ++ tailWord_2130094) baseStart_2130094 baseEnd_2130094 := by
    simpa [prefixWord, tailWord_2130094, baseEnd_2130094] using wordTrace_append hprefix tailTrace_2130094
  have hstable : (prefixWord ++ tailWord_2130094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130094).length < 2 ^ (prefixWord ++ tailWord_2130094).sum := by decide
  have hdescent : baseEnd_2130094 < baseStart_2130094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130239 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 6, 4]
def baseStart_2130239 : Nat := 118140960795 + 2130239 * 2 ^ 59
def prefixEnd_2130239 : Nat := 4983230072969 + 3 ^ 40 * 2130239 * 2
def baseEnd_2130239 : Nat := 364612171984398721271905

theorem tailTrace_2130239 : CollatzResearch.WordTrace tailWord_2130239 prefixEnd_2130239 364612171984398721271905 := by
  unfold tailWord_2130239
  simp only [CollatzResearch.WordTrace]
  refine ⟨77696199329515393701449771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51797466219676929134299847 77696199329515393701449771)
  ·
    refine ⟨116544298994273090552174657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77696199329515393701449771 116544298994273090552174657)
    ·
      refine ⟨87408224245704817914130993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116544298994273090552174657 87408224245704817914130993)
      ·
        refine ⟨65556168184278613435598245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87408224245704817914130993 65556168184278613435598245)
        ·
          refine ⟨12291781534552240019174671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65556168184278613435598245 12291781534552240019174671)
          ·
            refine ⟨18437672301828360028762007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12291781534552240019174671 18437672301828360028762007)
            ·
              refine ⟨27656508452742540043143011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18437672301828360028762007 27656508452742540043143011)
              ·
                refine ⟨41484762679113810064714517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27656508452742540043143011 41484762679113810064714517)
                ·
                  refine ⟨1944598250583459846783493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 41484762679113810064714517 1944598250583459846783493)
                  ·
                    refine ⟨364612171984398721271905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1944598250583459846783493 364612171984398721271905)
                    ·
                      rfl

theorem cell23_2130239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 6, 4].length) (baseStart_2130239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2130239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2130239 prefixEnd_2130239 := by exact prefixLift 2130239
  have htrace : WordTrace (prefixWord ++ tailWord_2130239) baseStart_2130239 baseEnd_2130239 := by
    simpa [prefixWord, tailWord_2130239, baseEnd_2130239] using wordTrace_append hprefix tailTrace_2130239
  have hstable : (prefixWord ++ tailWord_2130239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130239).length < 2 ^ (prefixWord ++ tailWord_2130239).sum := by decide
  have hdescent : baseEnd_2130239 < baseStart_2130239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130249 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 5, 2, 3]
def baseStart_2130249 : Nat := 118140960795 + 2130249 * 2 ^ 59
def prefixEnd_2130249 : Nat := 4983230072969 + 3 ^ 40 * 2130249 * 2
def baseEnd_2130249 : Nat := 1093841650759741124690669

theorem tailTrace_2130249 : CollatzResearch.WordTrace tailWord_2130249 prefixEnd_2130249 1093841650759741124690669 := by
  unfold tailWord_2130249
  simp only [CollatzResearch.WordTrace]
  refine ⟨77696564059479165409313801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51797709372986110272875867 77696564059479165409313801)
  ·
    refine ⟨58272423044609374056985351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77696564059479165409313801 58272423044609374056985351)
    ·
      refine ⟨87408634566914061085478027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58272423044609374056985351 87408634566914061085478027)
      ·
        refine ⟨131112951850371091628217041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87408634566914061085478027 131112951850371091628217041)
        ·
          refine ⟨98334713887778318721162781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131112951850371091628217041 98334713887778318721162781)
          ·
            refine ⟨36875517707916869520436043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98334713887778318721162781 36875517707916869520436043)
            ·
              refine ⟨55313276561875304280654065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36875517707916869520436043 55313276561875304280654065)
              ·
                refine ⟨41484957421406478210490549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55313276561875304280654065 41484957421406478210490549)
                ·
                  refine ⟨3889214758256857332233489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41484957421406478210490549 3889214758256857332233489)
                  ·
                    refine ⟨2916911068692642999175117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3889214758256857332233489 2916911068692642999175117)
                    ·
                      refine ⟨1093841650759741124690669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2916911068692642999175117 1093841650759741124690669)
                      ·
                        rfl

theorem cell23_2130249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5, 2, 3].length) (baseStart_2130249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2130249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2130249 prefixEnd_2130249 := by exact prefixLift 2130249
  have htrace : WordTrace (prefixWord ++ tailWord_2130249) baseStart_2130249 baseEnd_2130249 := by
    simpa [prefixWord, tailWord_2130249, baseEnd_2130249] using wordTrace_append hprefix tailTrace_2130249
  have hstable : (prefixWord ++ tailWord_2130249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130249).length < 2 ^ (prefixWord ++ tailWord_2130249).sum := by decide
  have hdescent : baseEnd_2130249 < baseStart_2130249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130313 : List Nat := [1, 2, 1, 1, 6, 1, 1, 4, 2, 1, 3]
def baseStart_2130313 : Nat := 118140960795 + 2130313 * 2 ^ 59
def prefixEnd_2130313 : Nat := 4983230072969 + 3 ^ 40 * 2130313 * 2
def baseEnd_2130313 : Nat := 1093874513521628874290375

theorem tailTrace_2130313 : CollatzResearch.WordTrace tailWord_2130313 prefixEnd_2130313 1093874513521628874290375 := by
  unfold tailWord_2130313
  simp only [CollatzResearch.WordTrace]
  refine ⟨77698898331247304339643593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51799265554164869559762395 77698898331247304339643593)
  ·
    refine ⟨58274173748435478254732695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77698898331247304339643593 58274173748435478254732695)
    ·
      refine ⟨87411260622653217382099043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58274173748435478254732695 87411260622653217382099043)
      ·
        refine ⟨131116890933979826073148565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87411260622653217382099043 131116890933979826073148565)
        ·
          refine ⟨6146104262530304347178839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 131116890933979826073148565 6146104262530304347178839)
          ·
            refine ⟨9219156393795456520768259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6146104262530304347178839 9219156393795456520768259)
            ·
              refine ⟨13828734590693184781152389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9219156393795456520768259 13828734590693184781152389)
              ·
                refine ⟨2592887735754972146466073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13828734590693184781152389 2592887735754972146466073)
                ·
                  refine ⟨1944665801816229109849555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2592887735754972146466073 1944665801816229109849555)
                  ·
                    refine ⟨2916998702724343664774333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1944665801816229109849555 2916998702724343664774333)
                    ·
                      refine ⟨1093874513521628874290375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2916998702724343664774333 1093874513521628874290375)
                      ·
                        rfl

theorem cell23_2130313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 4, 2, 1, 3].length) (baseStart_2130313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2130313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2130313 prefixEnd_2130313 := by exact prefixLift 2130313
  have htrace : WordTrace (prefixWord ++ tailWord_2130313) baseStart_2130313 baseEnd_2130313 := by
    simpa [prefixWord, tailWord_2130313, baseEnd_2130313] using wordTrace_append hprefix tailTrace_2130313
  have hstable : (prefixWord ++ tailWord_2130313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130313).length < 2 ^ (prefixWord ++ tailWord_2130313).sum := by decide
  have hdescent : baseEnd_2130313 < baseStart_2130313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130314 : List Nat := [3, 1, 2, 5, 1, 1, 1, 4, 1, 2, 2]
def baseStart_2130314 : Nat := 118140960795 + 2130314 * 2 ^ 59
def prefixEnd_2130314 : Nat := 4983230072969 + 3 ^ 40 * 2130314 * 2
def baseEnd_2130314 : Nat := 1093875027002283370377871

theorem tailTrace_2130314 : CollatzResearch.WordTrace tailWord_2130314 prefixEnd_2130314 1093875027002283370377871 := by
  unfold tailWord_2130314
  simp only [CollatzResearch.WordTrace]
  refine ⟨19424733701060920377607499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51799289869495787673619997 19424733701060920377607499)
  ·
    refine ⟨29137100551591380566411249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19424733701060920377607499 29137100551591380566411249)
    ·
      refine ⟨21852825413693535424808437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29137100551591380566411249 21852825413693535424808437)
      ·
        refine ⟨2048702382533768946075791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21852825413693535424808437 2048702382533768946075791)
        ·
          refine ⟨3073053573800653419113687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2048702382533768946075791 3073053573800653419113687)
          ·
            refine ⟨4609580360700980128670531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3073053573800653419113687 4609580360700980128670531)
            ·
              refine ⟨6914370541051470193005797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4609580360700980128670531 6914370541051470193005797)
              ·
                refine ⟨1296444476447150661188587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6914370541051470193005797 1296444476447150661188587)
                ·
                  refine ⟨1944666714670725991782881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1296444476447150661188587 1944666714670725991782881)
                  ·
                    refine ⟨1458500036003044493837161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1944666714670725991782881 1458500036003044493837161)
                    ·
                      refine ⟨1093875027002283370377871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1458500036003044493837161 1093875027002283370377871)
                      ·
                        rfl

theorem cell23_2130314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_2130314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2130314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2130314 prefixEnd_2130314 := by exact prefixLift 2130314
  have htrace : WordTrace (prefixWord ++ tailWord_2130314) baseStart_2130314 baseEnd_2130314 := by
    simpa [prefixWord, tailWord_2130314, baseEnd_2130314] using wordTrace_append hprefix tailTrace_2130314
  have hstable : (prefixWord ++ tailWord_2130314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130314).length < 2 ^ (prefixWord ++ tailWord_2130314).sum := by decide
  have hdescent : baseEnd_2130314 < baseStart_2130314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130329 : List Nat := [1, 2, 1, 2, 1, 4, 3, 1, 2, 6]
def baseStart_2130329 : Nat := 118140960795 + 2130329 * 2 ^ 59
def prefixEnd_2130329 : Nat := 4983230072969 + 3 ^ 40 * 2130329 * 2
def baseEnd_2130329 : Nat := 364627576404033603896767

theorem tailTrace_2130329 : CollatzResearch.WordTrace tailWord_2130329 prefixEnd_2130329 364627576404033603896767 := by
  unfold tailWord_2130329
  simp only [CollatzResearch.WordTrace]
  refine ⟨77699481899189339072226041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51799654599459559381484027 77699481899189339072226041)
  ·
    refine ⟨58274611424392004304169531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77699481899189339072226041 58274611424392004304169531)
    ·
      refine ⟨87411917136588006456254297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58274611424392004304169531 87411917136588006456254297)
      ·
        refine ⟨65558937852441004842190723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87411917136588006456254297 65558937852441004842190723)
        ·
          refine ⟨98338406778661507263286085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65558937852441004842190723 98338406778661507263286085)
          ·
            refine ⟨18438451270999032611866141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98338406778661507263286085 18438451270999032611866141)
            ·
              refine ⟨6914419226624637229449803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18438451270999032611866141 6914419226624637229449803)
              ·
                refine ⟨10371628839936955844174705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6914419226624637229449803 10371628839936955844174705)
                ·
                  refine ⟨7778721629952716883131029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10371628839936955844174705 7778721629952716883131029)
                  ·
                    refine ⟨364627576404033603896767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7778721629952716883131029 364627576404033603896767)
                    ·
                      rfl

theorem cell23_2130329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 6].length) (baseStart_2130329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2130329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2130329 prefixEnd_2130329 := by exact prefixLift 2130329
  have htrace : WordTrace (prefixWord ++ tailWord_2130329) baseStart_2130329 baseEnd_2130329 := by
    simpa [prefixWord, tailWord_2130329, baseEnd_2130329] using wordTrace_append hprefix tailTrace_2130329
  have hstable : (prefixWord ++ tailWord_2130329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130329).length < 2 ^ (prefixWord ++ tailWord_2130329).sum := by decide
  have hdescent : baseEnd_2130329 < baseStart_2130329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130353 : List Nat := [1, 2, 2, 4, 1, 2, 2, 2, 1, 4, 2]
def baseStart_2130353 : Nat := 118140960795 + 2130353 * 2 ^ 59
def prefixEnd_2130353 : Nat := 4983230072969 + 3 ^ 40 * 2130353 * 2
def baseEnd_2130353 : Nat := 1093895052747808717790191

theorem tailTrace_2130353 : CollatzResearch.WordTrace tailWord_2130353 prefixEnd_2130353 1093895052747808717790191 := by
  unfold tailWord_2130353
  simp only [CollatzResearch.WordTrace]
  refine ⟨77700357251102391171099713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51800238167401594114066475 77700357251102391171099713)
  ·
    refine ⟨58275267938326793378324785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77700357251102391171099713 58275267938326793378324785)
    ·
      refine ⟨43706450953745095033743589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58275267938326793378324785 43706450953745095033743589)
      ·
        refine ⟨8194959553827205318826923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43706450953745095033743589 8194959553827205318826923)
        ·
          refine ⟨12292439330740807978240385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8194959553827205318826923 12292439330740807978240385)
          ·
            refine ⟨9219329498055605983680289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12292439330740807978240385 9219329498055605983680289)
            ·
              refine ⟨6914497123541704487760217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9219329498055605983680289 6914497123541704487760217)
              ·
                refine ⟨5185872842656278365820163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6914497123541704487760217 5185872842656278365820163)
                ·
                  refine ⟨7778809263984417548730245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5185872842656278365820163 7778809263984417548730245)
                  ·
                    refine ⟨1458526736997078290386921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7778809263984417548730245 1458526736997078290386921)
                    ·
                      refine ⟨1093895052747808717790191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1458526736997078290386921 1093895052747808717790191)
                      ·
                        rfl

theorem cell23_2130353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_2130353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2130353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2130353 prefixEnd_2130353 := by exact prefixLift 2130353
  have htrace : WordTrace (prefixWord ++ tailWord_2130353) baseStart_2130353 baseEnd_2130353 := by
    simpa [prefixWord, tailWord_2130353, baseEnd_2130353] using wordTrace_append hprefix tailTrace_2130353
  have hstable : (prefixWord ++ tailWord_2130353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130353).length < 2 ^ (prefixWord ++ tailWord_2130353).sum := by decide
  have hdescent : baseEnd_2130353 < baseStart_2130353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130366 : List Nat := [4, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4]
def baseStart_2130366 : Nat := 118140960795 + 2130366 * 2 ^ 59
def prefixEnd_2130366 : Nat := 4983230072969 + 3 ^ 40 * 2130366 * 2
def baseEnd_2130366 : Nat := 1093901727996317166927631

theorem tailTrace_2130366 : CollatzResearch.WordTrace tailWord_2130366 prefixEnd_2130366 1093901727996317166927631 := by
  unfold tailWord_2130366
  simp only [CollatzResearch.WordTrace]
  refine ⟨9712603925006911798915369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51800554266703529594215301 9712603925006911798915369)
  ·
    refine ⟨7284452943755183849186527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9712603925006911798915369 7284452943755183849186527)
    ·
      refine ⟨10926679415632775773779791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7284452943755183849186527 10926679415632775773779791)
      ·
        refine ⟨16390019123449163660669687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10926679415632775773779791 16390019123449163660669687)
        ·
          refine ⟨24585028685173745491004531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16390019123449163660669687 24585028685173745491004531)
          ·
            refine ⟨36877543027760618236506797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24585028685173745491004531 36877543027760618236506797)
            ·
              refine ⟨13829078635410231838690049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36877543027760618236506797 13829078635410231838690049)
              ·
                refine ⟨10371808976557673879017537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13829078635410231838690049 10371808976557673879017537)
                ·
                  refine ⟨7778856732418255409263153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10371808976557673879017537 7778856732418255409263153)
                  ·
                    refine ⟨5834142549313691556947365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7778856732418255409263153 5834142549313691556947365)
                    ·
                      refine ⟨1093901727996317166927631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5834142549313691556947365 1093901727996317166927631)
                      ·
                        rfl

theorem cell23_2130366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_2130366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2130366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2130366 prefixEnd_2130366 := by exact prefixLift 2130366
  have htrace : WordTrace (prefixWord ++ tailWord_2130366) baseStart_2130366 baseEnd_2130366 := by
    simpa [prefixWord, tailWord_2130366, baseEnd_2130366] using wordTrace_append hprefix tailTrace_2130366
  have hstable : (prefixWord ++ tailWord_2130366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130366).length < 2 ^ (prefixWord ++ tailWord_2130366).sum := by decide
  have hdescent : baseEnd_2130366 < baseStart_2130366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130376 : List Nat := [2, 1, 3, 1, 3, 3, 2, 1, 7]
def baseStart_2130376 : Nat := 118140960795 + 2130376 * 2 ^ 59
def prefixEnd_2130376 : Nat := 4983230072969 + 3 ^ 40 * 2130376 * 2
def baseEnd_2130376 : Nat := 121545206978095791978065

theorem tailTrace_2130376 : CollatzResearch.WordTrace tailWord_2130376 prefixEnd_2130376 121545206978095791978065 := by
  unfold tailWord_2130376
  simp only [CollatzResearch.WordTrace]
  refine ⟨38850598065009533049593491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51800797420012710732791321 38850598065009533049593491)
  ·
    refine ⟨58275897097514299574390237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38850598065009533049593491 58275897097514299574390237)
    ·
      refine ⟨21853461411567862340396339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58275897097514299574390237 21853461411567862340396339)
      ·
        refine ⟨32780192117351793510594509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21853461411567862340396339 32780192117351793510594509)
        ·
          refine ⟨12292572044006922566472941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32780192117351793510594509 12292572044006922566472941)
          ·
            refine ⟨4609714516502595962427353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12292572044006922566472941 4609714516502595962427353)
            ·
              refine ⟨3457285887376946971820515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4609714516502595962427353 3457285887376946971820515)
              ·
                refine ⟨5185928831065420457730773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3457285887376946971820515 5185928831065420457730773)
                ·
                  refine ⟨121545206978095791978065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5185928831065420457730773 121545206978095791978065)
                  ·
                    rfl

theorem cell23_2130376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 7].length) (baseStart_2130376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2130376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2130376 prefixEnd_2130376 := by exact prefixLift 2130376
  have htrace : WordTrace (prefixWord ++ tailWord_2130376) baseStart_2130376 baseEnd_2130376 := by
    simpa [prefixWord, tailWord_2130376, baseEnd_2130376] using wordTrace_append hprefix tailTrace_2130376
  have hstable : (prefixWord ++ tailWord_2130376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130376).length < 2 ^ (prefixWord ++ tailWord_2130376).sum := by decide
  have hdescent : baseEnd_2130376 < baseStart_2130376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130410 : List Nat := [3, 1, 3, 1, 3, 3, 1, 3, 5]
def baseStart_2130410 : Nat := 118140960795 + 2130410 * 2 ^ 59
def prefixEnd_2130410 : Nat := 4983230072969 + 3 ^ 40 * 2130410 * 2
def baseEnd_2130410 : Nat := 121547146793901666086381

theorem tailTrace_2130410 : CollatzResearch.WordTrace tailWord_2130410 prefixEnd_2130410 121547146793901666086381 := by
  unfold tailWord_2130410
  simp only [CollatzResearch.WordTrace]
  refine ⟨19425609052973972476481171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51801624141263926603949789 19425609052973972476481171)
  ·
    refine ⟨29138413579460958714721757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19425609052973972476481171 29138413579460958714721757)
    ·
      refine ⟨10926905092297859518020659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29138413579460958714721757 10926905092297859518020659)
      ·
        refine ⟨16390357638446789277030989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10926905092297859518020659 16390357638446789277030989)
        ·
          refine ⟨6146384114417545978886621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16390357638446789277030989 6146384114417545978886621)
          ·
            refine ⟨2304894042906579742082483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6146384114417545978886621 2304894042906579742082483)
            ·
              refine ⟨3457341064359869613123725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2304894042906579742082483 3457341064359869613123725)
              ·
                refine ⟨1296502899134951104921397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3457341064359869613123725 1296502899134951104921397)
                ·
                  refine ⟨121547146793901666086381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1296502899134951104921397 121547146793901666086381)
                  ·
                    rfl

theorem cell23_2130410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 3, 5].length) (baseStart_2130410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2130410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2130410 prefixEnd_2130410 := by exact prefixLift 2130410
  have htrace : WordTrace (prefixWord ++ tailWord_2130410) baseStart_2130410 baseEnd_2130410 := by
    simpa [prefixWord, tailWord_2130410, baseEnd_2130410] using wordTrace_append hprefix tailTrace_2130410
  have hstable : (prefixWord ++ tailWord_2130410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130410).length < 2 ^ (prefixWord ++ tailWord_2130410).sum := by decide
  have hdescent : baseEnd_2130410 < baseStart_2130410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130438 : List Nat := [6, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2]
def baseStart_2130438 : Nat := 118140960795 + 2130438 * 2 ^ 59
def prefixEnd_2130438 : Nat := 4983230072969 + 3 ^ 40 * 2130438 * 2
def baseEnd_2130438 : Nat := 1093938698603440885227301

theorem tailTrace_2130438 : CollatzResearch.WordTrace tailWord_2130438 prefixEnd_2130438 1093938698603440885227301 := by
  unfold tailWord_2130438
  simp only [CollatzResearch.WordTrace]
  refine ⟨2428233045493576583998249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 51802304970529633791962645 2428233045493576583998249)
  ·
    refine ⟨1821174784120182437998687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2428233045493576583998249 1821174784120182437998687)
    ·
      refine ⟨2731762176180273656998031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1821174784120182437998687 2731762176180273656998031)
      ·
        refine ⟨4097643264270410485497047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2731762176180273656998031 4097643264270410485497047)
        ·
          refine ⟨6146464896405615728245571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4097643264270410485497047 6146464896405615728245571)
          ·
            refine ⟨9219697344608423592368357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6146464896405615728245571 9219697344608423592368357)
            ·
              refine ⟨1728693252114079423569067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9219697344608423592368357 1728693252114079423569067)
              ·
                refine ⟨2593039878171119135353601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1728693252114079423569067 2593039878171119135353601)
                ·
                  refine ⟨1944779908628339351515201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2593039878171119135353601 1944779908628339351515201)
                  ·
                    refine ⟨1458584931471254513636401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1944779908628339351515201 1458584931471254513636401)
                    ·
                      refine ⟨1093938698603440885227301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1458584931471254513636401 1093938698603440885227301)
                      ·
                        rfl

theorem cell23_2130438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_2130438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2130438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2130438 prefixEnd_2130438 := by exact prefixLift 2130438
  have htrace : WordTrace (prefixWord ++ tailWord_2130438) baseStart_2130438 baseEnd_2130438 := by
    simpa [prefixWord, tailWord_2130438, baseEnd_2130438] using wordTrace_append hprefix tailTrace_2130438
  have hstable : (prefixWord ++ tailWord_2130438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130438).length < 2 ^ (prefixWord ++ tailWord_2130438).sum := by decide
  have hdescent : baseEnd_2130438 < baseStart_2130438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130449 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 10]
def baseStart_2130449 : Nat := 118140960795 + 2130449 * 2 ^ 59
def prefixEnd_2130449 : Nat := 4983230072969 + 3 ^ 40 * 2130449 * 2
def baseEnd_2130449 : Nat := 121549371876737815798861

theorem tailTrace_2130449 : CollatzResearch.WordTrace tailWord_2130449 prefixEnd_2130449 121549371876737815798861 := by
  unfold tailWord_2130449
  simp only [CollatzResearch.WordTrace]
  refine ⟨77703858658754599566594401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51802572439169733044396267 77703858658754599566594401)
  ·
    refine ⟨58277893994065949674945801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77703858658754599566594401 58277893994065949674945801)
    ·
      refine ⟨43708420495549462256209351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58277893994065949674945801 43708420495549462256209351)
      ·
        refine ⟨65562630743324193384314027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43708420495549462256209351 65562630743324193384314027)
        ·
          refine ⟨98343946114986290076471041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65562630743324193384314027 98343946114986290076471041)
          ·
            refine ⟨73757959586239717557353281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98343946114986290076471041 73757959586239717557353281)
            ·
              refine ⟨55318469689679788168014961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73757959586239717557353281 55318469689679788168014961)
              ·
                refine ⟨41488852267259841126011221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55318469689679788168014961 41488852267259841126011221)
                ·
                  refine ⟨121549371876737815798861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 41488852267259841126011221 121549371876737815798861)
                  ·
                    rfl

theorem cell23_2130449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 10].length) (baseStart_2130449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2130449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2130449 prefixEnd_2130449 := by exact prefixLift 2130449
  have htrace : WordTrace (prefixWord ++ tailWord_2130449) baseStart_2130449 baseEnd_2130449 := by
    simpa [prefixWord, tailWord_2130449, baseEnd_2130449] using wordTrace_append hprefix tailTrace_2130449
  have hstable : (prefixWord ++ tailWord_2130449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130449).length < 2 ^ (prefixWord ++ tailWord_2130449).sum := by decide
  have hdescent : baseEnd_2130449 < baseStart_2130449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130496 : List Nat := [2, 1, 1, 2, 2, 2, 3, 2, 3, 5]
def baseStart_2130496 : Nat := 118140960795 + 2130496 * 2 ^ 59
def prefixEnd_2130496 : Nat := 4983230072969 + 3 ^ 40 * 2130496 * 2
def baseEnd_2130496 : Nat := 364656160160467219434011

theorem tailTrace_2130496 : CollatzResearch.WordTrace tailWord_2130496 prefixEnd_2130496 364656160160467219434011 := by
  unfold tailWord_2130496
  simp only [CollatzResearch.WordTrace]
  refine ⟨38852786444792163296777671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51803715259722884395703561 38852786444792163296777671)
  ·
    refine ⟨58279179667188244945166507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38852786444792163296777671 58279179667188244945166507)
    ·
      refine ⟨87418769500782367417749761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58279179667188244945166507 87418769500782367417749761)
      ·
        refine ⟨65564077125586775563312321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87418769500782367417749761 65564077125586775563312321)
        ·
          refine ⟨49173057844190081672484241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65564077125586775563312321 49173057844190081672484241)
          ·
            refine ⟨36879793383142561254363181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49173057844190081672484241 36879793383142561254363181)
            ·
              refine ⟨13829922518678460470386193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36879793383142561254363181 13829922518678460470386193)
              ·
                refine ⟨10372441889008845352789645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13829922518678460470386193 10372441889008845352789645)
                ·
                  refine ⟨3889665708378317007296117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10372441889008845352789645 3889665708378317007296117)
                  ·
                    refine ⟨364656160160467219434011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3889665708378317007296117 364656160160467219434011)
                    ·
                      rfl

theorem cell23_2130496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 3, 5].length) (baseStart_2130496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2130496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2130496 prefixEnd_2130496 := by exact prefixLift 2130496
  have htrace : WordTrace (prefixWord ++ tailWord_2130496) baseStart_2130496 baseEnd_2130496 := by
    simpa [prefixWord, tailWord_2130496, baseEnd_2130496] using wordTrace_append hprefix tailTrace_2130496
  have hstable : (prefixWord ++ tailWord_2130496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130496).length < 2 ^ (prefixWord ++ tailWord_2130496).sum := by decide
  have hdescent : baseEnd_2130496 < baseStart_2130496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130520 : List Nat := [2, 1, 2, 2, 1, 2, 5, 1, 2, 3, 2]
def baseStart_2130520 : Nat := 118140960795 + 2130520 * 2 ^ 59
def prefixEnd_2130520 : Nat := 4983230072969 + 3 ^ 40 * 2130520 * 2
def baseEnd_2130520 : Nat := 1093980804017109564401923

theorem tailTrace_2130520 : CollatzResearch.WordTrace tailWord_2130520 prefixEnd_2130520 1093980804017109564401923 := by
  unfold tailWord_2130520
  simp only [CollatzResearch.WordTrace]
  refine ⟨38853224120748689346214507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51804298827664919128286009 38853224120748689346214507)
  ·
    refine ⟨58279836181123034019321761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38853224120748689346214507 58279836181123034019321761)
    ·
      refine ⟨43709877135842275514491321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58279836181123034019321761 43709877135842275514491321)
      ·
        refine ⟨32782407851881706635868491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43709877135842275514491321 32782407851881706635868491)
        ·
          refine ⟨49173611777822559953802737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32782407851881706635868491 49173611777822559953802737)
          ·
            refine ⟨36880208833366919965352053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49173611777822559953802737 36880208833366919965352053)
            ·
              refine ⟨3457519578128148746751755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36880208833366919965352053 3457519578128148746751755)
              ·
                refine ⟨5186279367192223120127633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3457519578128148746751755 5186279367192223120127633)
                ·
                  refine ⟨3889709525394167340095725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5186279367192223120127633 3889709525394167340095725)
                  ·
                    refine ⟨1458641072022812752535897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3889709525394167340095725 1458641072022812752535897)
                    ·
                      refine ⟨1093980804017109564401923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1458641072022812752535897 1093980804017109564401923)
                      ·
                        rfl

theorem cell23_2130520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 2, 3, 2].length) (baseStart_2130520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2130520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2130520 prefixEnd_2130520 := by exact prefixLift 2130520
  have htrace : WordTrace (prefixWord ++ tailWord_2130520) baseStart_2130520 baseEnd_2130520 := by
    simpa [prefixWord, tailWord_2130520, baseEnd_2130520] using wordTrace_append hprefix tailTrace_2130520
  have hstable : (prefixWord ++ tailWord_2130520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130520).length < 2 ^ (prefixWord ++ tailWord_2130520).sum := by decide
  have hdescent : baseEnd_2130520 < baseStart_2130520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130553 : List Nat := [1, 2, 1, 3, 3, 3, 1, 2, 1, 1, 5]
def baseStart_2130553 : Nat := 118140960795 + 2130553 * 2 ^ 59
def prefixEnd_2130553 : Nat := 4983230072969 + 3 ^ 40 * 2130553 * 2
def baseEnd_2130553 : Nat := 1093997748878707935289271

theorem tailTrace_2130553 : CollatzResearch.WordTrace tailWord_2130553 prefixEnd_2130553 1093997748878707935289271 := by
  unfold tailWord_2130553
  simp only [CollatzResearch.WordTrace]
  refine ⟨77707651850377825328380313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51805101233585216885586875 77707651850377825328380313)
  ·
    refine ⟨58280738887783368996285235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77707651850377825328380313 58280738887783368996285235)
    ·
      refine ⟨87421108331675053494427853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58280738887783368996285235 87421108331675053494427853)
      ·
        refine ⟨32782915624378145060410445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87421108331675053494427853 32782915624378145060410445)
        ·
          refine ⟨12293593359141804397653917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32782915624378145060410445 12293593359141804397653917)
          ·
            refine ⟨4610097509678176649120219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12293593359141804397653917 4610097509678176649120219)
            ·
              refine ⟨6915146264517264973680329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4610097509678176649120219 6915146264517264973680329)
              ·
                refine ⟨5186359698387948730260247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6915146264517264973680329 5186359698387948730260247)
                ·
                  refine ⟨7779539547581923095390371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5186359698387948730260247 7779539547581923095390371)
                  ·
                    refine ⟨11669309321372884643085557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7779539547581923095390371 11669309321372884643085557)
                    ·
                      refine ⟨1093997748878707935289271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11669309321372884643085557 1093997748878707935289271)
                      ·
                        rfl

theorem cell23_2130553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_2130553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2130553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2130553 prefixEnd_2130553 := by exact prefixLift 2130553
  have htrace : WordTrace (prefixWord ++ tailWord_2130553) baseStart_2130553 baseEnd_2130553 := by
    simpa [prefixWord, tailWord_2130553, baseEnd_2130553] using wordTrace_append hprefix tailTrace_2130553
  have hstable : (prefixWord ++ tailWord_2130553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130553).length < 2 ^ (prefixWord ++ tailWord_2130553).sum := by decide
  have hdescent : baseEnd_2130553 < baseStart_2130553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130563 : List Nat := [1, 1, 1, 3, 3, 1, 5, 1, 1, 2, 4]
def baseStart_2130563 : Nat := 118140960795 + 2130563 * 2 ^ 59
def prefixEnd_2130563 : Nat := 4983230072969 + 3 ^ 40 * 2130563 * 2
def baseEnd_2130563 : Nat := 1094002883685252896164225

theorem tailTrace_2130563 : CollatzResearch.WordTrace tailWord_2130563 prefixEnd_2130563 1094002883685252896164225 := by
  unfold tailWord_2130563
  simp only [CollatzResearch.WordTrace]
  refine ⟨77708016580341597036244343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51805344386894398024162895 77708016580341597036244343)
  ·
    refine ⟨116562024870512395554366515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77708016580341597036244343 116562024870512395554366515)
    ·
      refine ⟨174843037305768593331549773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116562024870512395554366515 174843037305768593331549773)
      ·
        refine ⟨65566138989663222499331165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 174843037305768593331549773 65566138989663222499331165)
        ·
          refine ⟨24587302121123708437249187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65566138989663222499331165 24587302121123708437249187)
          ·
            refine ⟨36880953181685562655873781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24587302121123708437249187 36880953181685562655873781)
            ·
              refine ⟨3457589360783021498988167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36880953181685562655873781 3457589360783021498988167)
              ·
                refine ⟨5186384041174532248482251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3457589360783021498988167 5186384041174532248482251)
                ·
                  refine ⟨7779576061761798372723377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5186384041174532248482251 7779576061761798372723377)
                  ·
                    refine ⟨5834682046321348779542533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7779576061761798372723377 5834682046321348779542533)
                    ·
                      refine ⟨1094002883685252896164225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5834682046321348779542533 1094002883685252896164225)
                      ·
                        rfl

theorem cell23_2130563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 2, 4].length) (baseStart_2130563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2130563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2130563 prefixEnd_2130563 := by exact prefixLift 2130563
  have htrace : WordTrace (prefixWord ++ tailWord_2130563) baseStart_2130563 baseEnd_2130563 := by
    simpa [prefixWord, tailWord_2130563, baseEnd_2130563] using wordTrace_append hprefix tailTrace_2130563
  have hstable : (prefixWord ++ tailWord_2130563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130563).length < 2 ^ (prefixWord ++ tailWord_2130563).sum := by decide
  have hdescent : baseEnd_2130563 < baseStart_2130563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130583 : List Nat := [1, 1, 3, 3, 2, 1, 2, 1, 3, 3, 3]
def baseStart_2130583 : Nat := 118140960795 + 2130583 * 2 ^ 59
def prefixEnd_2130583 : Nat := 4983230072969 + 3 ^ 40 * 2130583 * 2
def baseEnd_2130583 : Nat := 1094013153298342817914133

theorem tailTrace_2130583 : CollatzResearch.WordTrace tailWord_2130583 prefixEnd_2130583 1094013153298342817914133 := by
  unfold tailWord_2130583
  simp only [CollatzResearch.WordTrace]
  refine ⟨77708746040269140451972403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51805830693512760301314935 77708746040269140451972403)
  ·
    refine ⟨116563119060403710677958605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77708746040269140451972403 116563119060403710677958605)
    ·
      refine ⟨43711169647651391504234477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116563119060403710677958605 43711169647651391504234477)
      ·
        refine ⟨16391688617869271814087929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43711169647651391504234477 16391688617869271814087929)
        ·
          refine ⟨12293766463401953860565947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16391688617869271814087929 12293766463401953860565947)
          ·
            refine ⟨18440649695102930790848921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12293766463401953860565947 18440649695102930790848921)
            ·
              refine ⟨13830487271327198093136691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18440649695102930790848921 13830487271327198093136691)
              ·
                refine ⟨20745730906990797139705037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13830487271327198093136691 20745730906990797139705037)
                ·
                  refine ⟨7779649090121548927389389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20745730906990797139705037 7779649090121548927389389)
                  ·
                    refine ⟨2917368408795580847771021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7779649090121548927389389 2917368408795580847771021)
                    ·
                      refine ⟨1094013153298342817914133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2917368408795580847771021 1094013153298342817914133)
                      ·
                        rfl

theorem cell23_2130583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_2130583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2130583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2130583 prefixEnd_2130583 := by exact prefixLift 2130583
  have htrace : WordTrace (prefixWord ++ tailWord_2130583) baseStart_2130583 baseEnd_2130583 := by
    simpa [prefixWord, tailWord_2130583, baseEnd_2130583] using wordTrace_append hprefix tailTrace_2130583
  have hstable : (prefixWord ++ tailWord_2130583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130583).length < 2 ^ (prefixWord ++ tailWord_2130583).sum := by decide
  have hdescent : baseEnd_2130583 < baseStart_2130583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130610 : List Nat := [3, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2]
def baseStart_2130610 : Nat := 118140960795 + 2130610 * 2 ^ 59
def prefixEnd_2130610 : Nat := 4983230072969 + 3 ^ 40 * 2130610 * 2
def baseEnd_2130610 : Nat := 1094027017276014212276509

theorem tailTrace_2130610 : CollatzResearch.WordTrace tailWord_2130610 prefixEnd_2130610 1094027017276014212276509 := by
  unfold tailWord_2130610
  simp only [CollatzResearch.WordTrace]
  refine ⟨19427432702792831015801321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51806487207447549375470189 19427432702792831015801321)
  ·
    refine ⟨14570574527094623261850991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19427432702792831015801321 14570574527094623261850991)
    ·
      refine ⟨21855861790641934892776487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14570574527094623261850991 21855861790641934892776487)
      ·
        refine ⟨32783792685962902339164731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21855861790641934892776487 32783792685962902339164731)
        ·
          refine ⟨49175689028944353508747097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32783792685962902339164731 49175689028944353508747097)
          ·
            refine ⟨36881766771708265131560323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49175689028944353508747097 36881766771708265131560323)
            ·
              refine ⟨55322650157562397697340485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36881766771708265131560323 55322650157562397697340485)
              ·
                refine ⟨10372996904542949568251341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55322650157562397697340485 10372996904542949568251341)
                ·
                  refine ⟨3889873839203606088094253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10372996904542949568251341 3889873839203606088094253)
                  ·
                    refine ⟨1458702689701352283035345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3889873839203606088094253 1458702689701352283035345)
                    ·
                      refine ⟨1094027017276014212276509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1458702689701352283035345 1094027017276014212276509)
                      ·
                        rfl

theorem cell23_2130610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2].length) (baseStart_2130610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2130610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2130610 prefixEnd_2130610 := by exact prefixLift 2130610
  have htrace : WordTrace (prefixWord ++ tailWord_2130610) baseStart_2130610 baseEnd_2130610 := by
    simpa [prefixWord, tailWord_2130610, baseEnd_2130610] using wordTrace_append hprefix tailTrace_2130610
  have hstable : (prefixWord ++ tailWord_2130610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130610).length < 2 ^ (prefixWord ++ tailWord_2130610).sum := by decide
  have hdescent : baseEnd_2130610 < baseStart_2130610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130670 : List Nat := [4, 1, 2, 1, 1, 4, 1, 1, 2, 2, 4]
def baseStart_2130670 : Nat := 118140960795 + 2130670 * 2 ^ 59
def prefixEnd_2130670 : Nat := 4983230072969 + 3 ^ 40 * 2130670 * 2
def baseEnd_2130670 : Nat := 1094057826115283977526233

theorem tailTrace_2130670 : CollatzResearch.WordTrace tailWord_2130670 prefixEnd_2130670 1094057826115283977526233 := by
  unfold tailWord_2130670
  simp only [CollatzResearch.WordTrace]
  refine ⟨9713989898869244288798683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51807946127302636206926309 9713989898869244288798683)
  ·
    refine ⟨14570984848303866433198025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9713989898869244288798683 14570984848303866433198025)
    ·
      refine ⟨10928238636227899824898519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14570984848303866433198025 10928238636227899824898519)
      ·
        refine ⟨16392357954341849737347779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10928238636227899824898519 16392357954341849737347779)
        ·
          refine ⟨24588536931512774606021669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16392357954341849737347779 24588536931512774606021669)
          ·
            refine ⟨4610350674658645238629063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24588536931512774606021669 4610350674658645238629063)
            ·
              refine ⟨6915526011987967857943595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4610350674658645238629063 6915526011987967857943595)
              ·
                refine ⟨10373289017981951786915393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6915526011987967857943595 10373289017981951786915393)
                ·
                  refine ⟨7779966763486463840186545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10373289017981951786915393 7779966763486463840186545)
                  ·
                    refine ⟨5834975072614847880139909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7779966763486463840186545 5834975072614847880139909)
                    ·
                      refine ⟨1094057826115283977526233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5834975072614847880139909 1094057826115283977526233)
                      ·
                        rfl

theorem cell23_2130670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_2130670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2130670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2130670 prefixEnd_2130670 := by exact prefixLift 2130670
  have htrace : WordTrace (prefixWord ++ tailWord_2130670) baseStart_2130670 baseEnd_2130670 := by
    simpa [prefixWord, tailWord_2130670, baseEnd_2130670] using wordTrace_append hprefix tailTrace_2130670
  have hstable : (prefixWord ++ tailWord_2130670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130670).length < 2 ^ (prefixWord ++ tailWord_2130670).sum := by decide
  have hdescent : baseEnd_2130670 < baseStart_2130670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130674 : List Nat := [3, 2, 1, 3, 1, 2, 2, 3, 2, 2, 2]
def baseStart_2130674 : Nat := 118140960795 + 2130674 * 2 ^ 59
def prefixEnd_2130674 : Nat := 4983230072969 + 3 ^ 40 * 2130674 * 2
def baseEnd_2130674 : Nat := 1094059880037901961876215

theorem tailTrace_2130674 : CollatzResearch.WordTrace tailWord_2130674 prefixEnd_2130674 1094059880037901961876215 := by
  unfold tailWord_2130674
  simp only [CollatzResearch.WordTrace]
  refine ⟨19428016270734865748383769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51808043388626308662356717 19428016270734865748383769)
  ·
    refine ⟨14571012203051149311287827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19428016270734865748383769 14571012203051149311287827)
    ·
      refine ⟨21856518304576723966931741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14571012203051149311287827 21856518304576723966931741)
      ·
        refine ⟨8196194364216271487599403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21856518304576723966931741 8196194364216271487599403)
        ·
          refine ⟨12294291546324407231399105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8196194364216271487599403 12294291546324407231399105)
          ·
            refine ⟨9220718659743305423549329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12294291546324407231399105 9220718659743305423549329)
            ·
              refine ⟨6915538994807479067661997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9220718659743305423549329 6915538994807479067661997)
              ·
                refine ⟨2593327123052804650373249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6915538994807479067661997 2593327123052804650373249)
                ·
                  refine ⟨1944995342289603487779937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2593327123052804650373249 1944995342289603487779937)
                  ·
                    refine ⟨1458746506717202615834953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1944995342289603487779937 1458746506717202615834953)
                    ·
                      refine ⟨1094059880037901961876215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1458746506717202615834953 1094059880037901961876215)
                      ·
                        rfl

theorem cell23_2130674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_2130674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2130674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2130674 prefixEnd_2130674 := by exact prefixLift 2130674
  have htrace : WordTrace (prefixWord ++ tailWord_2130674) baseStart_2130674 baseEnd_2130674 := by
    simpa [prefixWord, tailWord_2130674, baseEnd_2130674] using wordTrace_append hprefix tailTrace_2130674
  have hstable : (prefixWord ++ tailWord_2130674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130674).length < 2 ^ (prefixWord ++ tailWord_2130674).sum := by decide
  have hdescent : baseEnd_2130674 < baseStart_2130674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130743 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 2, 4, 4]
def baseStart_2130743 : Nat := 118140960795 + 2130743 * 2 ^ 59
def prefixEnd_2130743 : Nat := 4983230072969 + 3 ^ 40 * 2130743 * 2
def baseEnd_2130743 : Nat := 1094095310203062191913397

theorem tailTrace_2130743 : CollatzResearch.WordTrace tailWord_2130743 prefixEnd_2130743 1094095310203062191913397 := by
  unfold tailWord_2130743
  simp only [CollatzResearch.WordTrace]
  refine ⟨77714581719689487777796883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51809721146459658518531255 77714581719689487777796883)
  ·
    refine ⟨116571872579534231666695325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77714581719689487777796883 116571872579534231666695325)
    ·
      refine ⟨43714452217325336875010747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116571872579534231666695325 43714452217325336875010747)
      ·
        refine ⟨65571678325988005312516121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43714452217325336875010747 65571678325988005312516121)
        ·
          refine ⟨49178758744491003984387091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65571678325988005312516121 49178758744491003984387091)
          ·
            refine ⟨73768138116736505976580637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49178758744491003984387091 73768138116736505976580637)
            ·
              refine ⟨27663051793776189741217739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73768138116736505976580637 27663051793776189741217739)
              ·
                refine ⟨41494577690664284611826609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27663051793776189741217739 41494577690664284611826609)
                ·
                  refine ⟨31120933267998213458869957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41494577690664284611826609 31120933267998213458869957)
                  ·
                    refine ⟨5835174987749665023538117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31120933267998213458869957 5835174987749665023538117)
                    ·
                      refine ⟨1094095310203062191913397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5835174987749665023538117 1094095310203062191913397)
                      ·
                        rfl

theorem cell23_2130743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 4, 4].length) (baseStart_2130743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2130743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2130743 prefixEnd_2130743 := by exact prefixLift 2130743
  have htrace : WordTrace (prefixWord ++ tailWord_2130743) baseStart_2130743 baseEnd_2130743 := by
    simpa [prefixWord, tailWord_2130743, baseEnd_2130743] using wordTrace_append hprefix tailTrace_2130743
  have hstable : (prefixWord ++ tailWord_2130743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130743).length < 2 ^ (prefixWord ++ tailWord_2130743).sum := by decide
  have hdescent : baseEnd_2130743 < baseStart_2130743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130757 : List Nat := [1, 3, 1, 1, 1, 2, 2, 7, 1, 4]
def baseStart_2130757 : Nat := 118140960795 + 2130757 * 2 ^ 59
def prefixEnd_2130757 : Nat := 4983230072969 + 3 ^ 40 * 2130757 * 2
def baseEnd_2130757 : Nat := 364700832977408379046111

theorem tailTrace_2130757 : CollatzResearch.WordTrace tailWord_2130757 prefixEnd_2130757 364700832977408379046111 := by
  unfold tailWord_2130757
  simp only [CollatzResearch.WordTrace]
  refine ⟨77715092341638768168806525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51810061561092512112537683 77715092341638768168806525)
  ·
    refine ⟨29143159628114538063302447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77715092341638768168806525 29143159628114538063302447)
    ·
      refine ⟨43714739442171807094953671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29143159628114538063302447 43714739442171807094953671)
      ·
        refine ⟨65572109163257710642430507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43714739442171807094953671 65572109163257710642430507)
        ·
          refine ⟨98358163744886565963645761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65572109163257710642430507 98358163744886565963645761)
          ·
            refine ⟨73768622808664924472734321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98358163744886565963645761 73768622808664924472734321)
            ·
              refine ⟨55326467106498693354550741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73768622808664924472734321 55326467106498693354550741)
              ·
                refine ⟨1296714072808563125497283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 55326467106498693354550741 1296714072808563125497283)
                ·
                  refine ⟨1945071109212844688245925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1296714072808563125497283 1945071109212844688245925)
                  ·
                    refine ⟨364700832977408379046111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1945071109212844688245925 364700832977408379046111)
                    ·
                      rfl

theorem cell23_2130757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 7, 1, 4].length) (baseStart_2130757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2130757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2130757 prefixEnd_2130757 := by exact prefixLift 2130757
  have htrace : WordTrace (prefixWord ++ tailWord_2130757) baseStart_2130757 baseEnd_2130757 := by
    simpa [prefixWord, tailWord_2130757, baseEnd_2130757] using wordTrace_append hprefix tailTrace_2130757
  have hstable : (prefixWord ++ tailWord_2130757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130757).length < 2 ^ (prefixWord ++ tailWord_2130757).sum := by decide
  have hdescent : baseEnd_2130757 < baseStart_2130757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130770 : List Nat := [3, 2, 2, 1, 1, 2, 2, 4, 6]
def baseStart_2130770 : Nat := 118140960795 + 2130770 * 2 ^ 59
def prefixEnd_2130770 : Nat := 4983230072969 + 3 ^ 40 * 2130770 * 2
def baseEnd_2130770 : Nat := 121567686020081509586197

theorem tailTrace_2130770 : CollatzResearch.WordTrace tailWord_2130770 prefixEnd_2130770 121567686020081509586197 := by
  unfold tailWord_2130770
  simp only [CollatzResearch.WordTrace]
  refine ⟨19428891622647917847257441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51810377660394447592686509 19428891622647917847257441)
  ·
    refine ⟨14571668716985938385443081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19428891622647917847257441 14571668716985938385443081)
    ·
      refine ⟨10928751537739453789082311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14571668716985938385443081 10928751537739453789082311)
      ·
        refine ⟨16393127306609180683623467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10928751537739453789082311 16393127306609180683623467)
        ·
          refine ⟨24589690959913771025435201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16393127306609180683623467 24589690959913771025435201)
          ·
            refine ⟨18442268219935328269076401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24589690959913771025435201 18442268219935328269076401)
            ·
              refine ⟨13831701164951496201807301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18442268219935328269076401 13831701164951496201807301)
              ·
                refine ⟨2593443968428405537838869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13831701164951496201807301 2593443968428405537838869)
                ·
                  refine ⟨121567686020081509586197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2593443968428405537838869 121567686020081509586197)
                  ·
                    rfl

theorem cell23_2130770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 4, 6].length) (baseStart_2130770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2130770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2130770 prefixEnd_2130770 := by exact prefixLift 2130770
  have htrace : WordTrace (prefixWord ++ tailWord_2130770) baseStart_2130770 baseEnd_2130770 := by
    simpa [prefixWord, tailWord_2130770, baseEnd_2130770] using wordTrace_append hprefix tailTrace_2130770
  have hstable : (prefixWord ++ tailWord_2130770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130770).length < 2 ^ (prefixWord ++ tailWord_2130770).sum := by decide
  have hdescent : baseEnd_2130770 < baseStart_2130770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130787 : List Nat := [1, 1, 1, 5, 3, 1, 4, 1, 6]
def baseStart_2130787 : Nat := 118140960795 + 2130787 * 2 ^ 59
def prefixEnd_2130787 : Nat := 4983230072969 + 3 ^ 40 * 2130787 * 2
def baseEnd_2130787 : Nat := 121568655927984446640355

theorem tailTrace_2130787 : CollatzResearch.WordTrace tailWord_2130787 prefixEnd_2130787 121568655927984446640355 := by
  unfold tailWord_2130787
  simp only [CollatzResearch.WordTrace]
  refine ⟨77716186531530083292398615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51810791021020055528265743 77716186531530083292398615)
  ·
    refine ⟨116574279797295124938597923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77716186531530083292398615 116574279797295124938597923)
    ·
      refine ⟨174861419695942687407896885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116574279797295124938597923 174861419695942687407896885)
      ·
        refine ⟨16393258096494626944490333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 174861419695942687407896885 16393258096494626944490333)
        ·
          refine ⟨6147471786185485104183875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16393258096494626944490333 6147471786185485104183875)
          ·
            refine ⟨9221207679278227656275813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6147471786185485104183875 9221207679278227656275813)
            ·
              refine ⟨1728976439864667685551715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9221207679278227656275813 1728976439864667685551715)
              ·
                refine ⟨2593464659797001528327573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1728976439864667685551715 2593464659797001528327573)
                ·
                  refine ⟨121568655927984446640355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2593464659797001528327573 121568655927984446640355)
                  ·
                    rfl

theorem cell23_2130787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 1, 6].length) (baseStart_2130787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2130787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2130787 prefixEnd_2130787 := by exact prefixLift 2130787
  have htrace : WordTrace (prefixWord ++ tailWord_2130787) baseStart_2130787 baseEnd_2130787 := by
    simpa [prefixWord, tailWord_2130787, baseEnd_2130787] using wordTrace_append hprefix tailTrace_2130787
  have hstable : (prefixWord ++ tailWord_2130787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130787).length < 2 ^ (prefixWord ++ tailWord_2130787).sum := by decide
  have hdescent : baseEnd_2130787 < baseStart_2130787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130797 : List Nat := [1, 5, 1, 1, 1, 1, 1, 3, 5, 1, 3]
def baseStart_2130797 : Nat := 118140960795 + 2130797 * 2 ^ 59
def prefixEnd_2130797 : Nat := 4983230072969 + 3 ^ 40 * 2130797 * 2
def baseEnd_2130797 : Nat := 1094123038158404980638149

theorem tailTrace_2130797 : CollatzResearch.WordTrace tailWord_2130797 prefixEnd_2130797 1094123038158404980638149 := by
  unfold tailWord_2130797
  simp only [CollatzResearch.WordTrace]
  refine ⟨77716551261493855000262645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51811034174329236666841763 77716551261493855000262645)
  ·
    refine ⟨7285926680765048906274623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77716551261493855000262645 7285926680765048906274623)
    ·
      refine ⟨10928890021147573359411935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7285926680765048906274623 10928890021147573359411935)
      ·
        refine ⟨16393335031721360039117903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10928890021147573359411935 16393335031721360039117903)
        ·
          refine ⟨24590002547582040058676855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16393335031721360039117903 24590002547582040058676855)
          ·
            refine ⟨36885003821373060088015283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24590002547582040058676855 36885003821373060088015283)
            ·
              refine ⟨55327505732059590132022925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36885003821373060088015283 55327505732059590132022925)
              ·
                refine ⟨20747814649522346299508597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55327505732059590132022925 20747814649522346299508597)
                ·
                  refine ⟨1945107623392719965578931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20747814649522346299508597 1945107623392719965578931)
                  ·
                    refine ⟨2917661435089079948368397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1945107623392719965578931 2917661435089079948368397)
                    ·
                      refine ⟨1094123038158404980638149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2917661435089079948368397 1094123038158404980638149)
                      ·
                        rfl

theorem cell23_2130797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_2130797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2130797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2130797 prefixEnd_2130797 := by exact prefixLift 2130797
  have htrace : WordTrace (prefixWord ++ tailWord_2130797) baseStart_2130797 baseEnd_2130797 := by
    simpa [prefixWord, tailWord_2130797, baseEnd_2130797] using wordTrace_append hprefix tailTrace_2130797
  have hstable : (prefixWord ++ tailWord_2130797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130797).length < 2 ^ (prefixWord ++ tailWord_2130797).sum := by decide
  have hdescent : baseEnd_2130797 < baseStart_2130797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130824 : List Nat := [2, 1, 3, 3, 2, 1, 2, 2, 2, 3, 2]
def baseStart_2130824 : Nat := 118140960795 + 2130824 * 2 ^ 59
def prefixEnd_2130824 : Nat := 4983230072969 + 3 ^ 40 * 2130824 * 2
def baseEnd_2130824 : Nat := 1094136902136076375000525

theorem tailTrace_2130824 : CollatzResearch.WordTrace tailWord_2130824 prefixEnd_2130824 1094136902136076375000525 := by
  unfold tailWord_2130824
  simp only [CollatzResearch.WordTrace]
  refine ⟨38858768016198019305747763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51811690688264025740997017 38858768016198019305747763)
  ·
    refine ⟨58288152024297028958621645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38858768016198019305747763 58288152024297028958621645)
    ·
      refine ⟨21858057009111385859483117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58288152024297028958621645 21858057009111385859483117)
      ·
        refine ⟨8196771378416769697306169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21858057009111385859483117 8196771378416769697306169)
        ·
          refine ⟨6147578533812577272979627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8196771378416769697306169 6147578533812577272979627)
          ·
            refine ⟨9221367800718865909469441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6147578533812577272979627 9221367800718865909469441)
            ·
              refine ⟨6916025850539149432102081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9221367800718865909469441 6916025850539149432102081)
              ·
                refine ⟨5187019387904362074076561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6916025850539149432102081 5187019387904362074076561)
                ·
                  refine ⟨3890264540928271555557421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5187019387904362074076561 3890264540928271555557421)
                  ·
                    refine ⟨1458849202848101833334033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3890264540928271555557421 1458849202848101833334033)
                    ·
                      refine ⟨1094136902136076375000525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1458849202848101833334033 1094136902136076375000525)
                      ·
                        rfl

theorem cell23_2130824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_2130824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2130824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2130824 prefixEnd_2130824 := by exact prefixLift 2130824
  have htrace : WordTrace (prefixWord ++ tailWord_2130824) baseStart_2130824 baseEnd_2130824 := by
    simpa [prefixWord, tailWord_2130824, baseEnd_2130824] using wordTrace_append hprefix tailTrace_2130824
  have hstable : (prefixWord ++ tailWord_2130824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130824).length < 2 ^ (prefixWord ++ tailWord_2130824).sum := by decide
  have hdescent : baseEnd_2130824 < baseStart_2130824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130847 : List Nat := [1, 1, 2, 5, 2, 2, 2, 1, 1, 6]
def baseStart_2130847 : Nat := 118140960795 + 2130847 * 2 ^ 59
def prefixEnd_2130847 : Nat := 4983230072969 + 3 ^ 40 * 2130847 * 2
def baseEnd_2130847 : Nat := 364716237397043261670973

theorem tailTrace_2130847 : CollatzResearch.WordTrace tailWord_2130847 prefixEnd_2130847 364716237397043261670973 := by
  unfold tailWord_2130847
  simp only [CollatzResearch.WordTrace]
  refine ⟨77718374911312713539582795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51812249940875142359721863 77718374911312713539582795)
  ·
    refine ⟨116577562366969070309374193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77718374911312713539582795 116577562366969070309374193)
    ·
      refine ⟨87433171775226802732030645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116577562366969070309374193 87433171775226802732030645)
      ·
        refine ⟨8196859853927512756127873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 87433171775226802732030645 8196859853927512756127873)
        ·
          refine ⟨6147644890445634567095905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8196859853927512756127873 6147644890445634567095905)
          ·
            refine ⟨4610733667834225925321929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6147644890445634567095905 4610733667834225925321929)
            ·
              refine ⟨3458050250875669443991447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4610733667834225925321929 3458050250875669443991447)
              ·
                refine ⟨5187075376313504165987171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3458050250875669443991447 5187075376313504165987171)
                ·
                  refine ⟨7780613064470256248980757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5187075376313504165987171 7780613064470256248980757)
                  ·
                    refine ⟨364716237397043261670973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7780613064470256248980757 364716237397043261670973)
                    ·
                      rfl

theorem cell23_2130847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 6].length) (baseStart_2130847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2130847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2130847 prefixEnd_2130847 := by exact prefixLift 2130847
  have htrace : WordTrace (prefixWord ++ tailWord_2130847) baseStart_2130847 baseEnd_2130847 := by
    simpa [prefixWord, tailWord_2130847, baseEnd_2130847] using wordTrace_append hprefix tailTrace_2130847
  have hstable : (prefixWord ++ tailWord_2130847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130847).length < 2 ^ (prefixWord ++ tailWord_2130847).sum := by decide
  have hdescent : baseEnd_2130847 < baseStart_2130847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130857 : List Nat := [1, 2, 1, 1, 1, 1, 6, 4, 1, 2, 3]
def baseStart_2130857 : Nat := 118140960795 + 2130857 * 2 ^ 59
def prefixEnd_2130857 : Nat := 4983230072969 + 3 ^ 40 * 2130857 * 2
def baseEnd_2130857 : Nat := 1094153846997674745887873

theorem tailTrace_2130857 : CollatzResearch.WordTrace tailWord_2130857 prefixEnd_2130857 1094153846997674745887873 := by
  unfold tailWord_2130857
  simp only [CollatzResearch.WordTrace]
  refine ⟨77718739641276485247446825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51812493094184323498297883 77718739641276485247446825)
  ·
    refine ⟨58289054730957363935585119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77718739641276485247446825 58289054730957363935585119)
    ·
      refine ⟨87433582096436045903377679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58289054730957363935585119 87433582096436045903377679)
      ·
        refine ⟨131150373144654068855066519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87433582096436045903377679 131150373144654068855066519)
        ·
          refine ⟨196725559716981103282599779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131150373144654068855066519 196725559716981103282599779)
          ·
            refine ⟨295088339575471654923899669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196725559716981103282599779 295088339575471654923899669)
            ·
              refine ⟨13832265917600233824557797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 295088339575471654923899669 13832265917600233824557797)
              ·
                refine ⟨2593549859550043842104587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13832265917600233824557797 2593549859550043842104587)
                ·
                  refine ⟨3890324789325065763156881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2593549859550043842104587 3890324789325065763156881)
                  ·
                    refine ⟨2917743591993799322367661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3890324789325065763156881 2917743591993799322367661)
                    ·
                      refine ⟨1094153846997674745887873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2917743591993799322367661 1094153846997674745887873)
                      ·
                        rfl

theorem cell23_2130857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 4, 1, 2, 3].length) (baseStart_2130857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2130857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2130857 prefixEnd_2130857 := by exact prefixLift 2130857
  have htrace : WordTrace (prefixWord ++ tailWord_2130857) baseStart_2130857 baseEnd_2130857 := by
    simpa [prefixWord, tailWord_2130857, baseEnd_2130857] using wordTrace_append hprefix tailTrace_2130857
  have hstable : (prefixWord ++ tailWord_2130857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130857).length < 2 ^ (prefixWord ++ tailWord_2130857).sum := by decide
  have hdescent : baseEnd_2130857 < baseStart_2130857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130868 : List Nat := [2, 5, 2, 1, 1, 3, 2, 1, 1, 5]
def baseStart_2130868 : Nat := 118140960795 + 2130868 * 2 ^ 59
def prefixEnd_2130868 : Nat := 4983230072969 + 3 ^ 40 * 2130868 * 2
def baseEnd_2130868 : Nat := 364719831761624734283441

theorem tailTrace_2130868 : CollatzResearch.WordTrace tailWord_2130868 prefixEnd_2130868 364719831761624734283441 := by
  unfold tailWord_2130868
  simp only [CollatzResearch.WordTrace]
  refine ⟨38859570422118317063048629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51812760562824422750731505 38859570422118317063048629)
  ·
    refine ⟨3643084727073592224660809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38859570422118317063048629 3643084727073592224660809)
    ·
      refine ⟨2732313545305194168495607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3643084727073592224660809 2732313545305194168495607)
      ·
        refine ⟨4098470317957791252743411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2732313545305194168495607 4098470317957791252743411)
        ·
          refine ⟨6147705476936686879115117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4098470317957791252743411 6147705476936686879115117)
          ·
            refine ⟨2305389553851257579668169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6147705476936686879115117 2305389553851257579668169)
            ·
              refine ⟨1729042165388443184751127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2305389553851257579668169 1729042165388443184751127)
              ·
                refine ⟨2593563248082664777126691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1729042165388443184751127 2593563248082664777126691)
                ·
                  refine ⟨3890344872123997165690037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2593563248082664777126691 3890344872123997165690037)
                  ·
                    refine ⟨364719831761624734283441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3890344872123997165690037 364719831761624734283441)
                    ·
                      rfl

theorem cell23_2130868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_2130868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2130868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2130868 prefixEnd_2130868 := by exact prefixLift 2130868
  have htrace : WordTrace (prefixWord ++ tailWord_2130868) baseStart_2130868 baseEnd_2130868 := by
    simpa [prefixWord, tailWord_2130868, baseEnd_2130868] using wordTrace_append hprefix tailTrace_2130868
  have hstable : (prefixWord ++ tailWord_2130868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130868).length < 2 ^ (prefixWord ++ tailWord_2130868).sum := by decide
  have hdescent : baseEnd_2130868 < baseStart_2130868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130871 : List Nat := [1, 1, 3, 1, 3, 1, 3, 5, 1, 2, 2]
def baseStart_2130871 : Nat := 118140960795 + 2130871 * 2 ^ 59
def prefixEnd_2130871 : Nat := 4983230072969 + 3 ^ 40 * 2130871 * 2
def baseEnd_2130871 : Nat := 1094161035726837691112809

theorem tailTrace_2130871 : CollatzResearch.WordTrace tailWord_2130871 prefixEnd_2130871 1094161035726837691112809 := by
  unfold tailWord_2130871
  simp only [CollatzResearch.WordTrace]
  refine ⟨77719250263225765638456467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51812833508817177092304311 77719250263225765638456467)
  ·
    refine ⟨116578875394838648457684701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77719250263225765638456467 116578875394838648457684701)
    ·
      refine ⟨43717078273064493171631763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116578875394838648457684701 43717078273064493171631763)
      ·
        refine ⟨65575617409596739757447645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43717078273064493171631763 65575617409596739757447645)
        ·
          refine ⟨24590856528598777409042867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65575617409596739757447645 24590856528598777409042867)
          ·
            refine ⟨36886284792898166113564301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24590856528598777409042867 36886284792898166113564301)
            ·
              refine ⟨13832356797336812292586613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36886284792898166113564301 13832356797336812292586613)
              ·
                refine ⟨1296783449750326152429995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13832356797336812292586613 1296783449750326152429995)
                ·
                  refine ⟨1945175174625489228644993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1296783449750326152429995 1945175174625489228644993)
                  ·
                    refine ⟨1458881380969116921483745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1945175174625489228644993 1458881380969116921483745)
                    ·
                      refine ⟨1094161035726837691112809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1458881380969116921483745 1094161035726837691112809)
                      ·
                        rfl

theorem cell23_2130871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 5, 1, 2, 2].length) (baseStart_2130871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2130871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2130871 prefixEnd_2130871 := by exact prefixLift 2130871
  have htrace : WordTrace (prefixWord ++ tailWord_2130871) baseStart_2130871 baseEnd_2130871 := by
    simpa [prefixWord, tailWord_2130871, baseEnd_2130871] using wordTrace_append hprefix tailTrace_2130871
  have hstable : (prefixWord ++ tailWord_2130871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130871).length < 2 ^ (prefixWord ++ tailWord_2130871).sum := by decide
  have hdescent : baseEnd_2130871 < baseStart_2130871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130901 : List Nat := [1, 3, 2, 3, 4, 1, 1, 1, 1, 2, 4]
def baseStart_2130901 : Nat := 118140960795 + 2130901 * 2 ^ 59
def prefixEnd_2130901 : Nat := 4983230072969 + 3 ^ 40 * 2130901 * 2
def baseEnd_2130901 : Nat := 1094176440146472573737671

theorem tailTrace_2130901 : CollatzResearch.WordTrace tailWord_2130901 prefixEnd_2130901 1094176440146472573737671 := by
  unfold tailWord_2130901
  simp only [CollatzResearch.WordTrace]
  refine ⟨77720344453117080762048557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51813562968744720508032371 77720344453117080762048557)
  ·
    refine ⟨29145129169918905285768209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77720344453117080762048557 29145129169918905285768209)
    ·
      refine ⟨21858846877439178964326157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29145129169918905285768209 21858846877439178964326157)
      ·
        refine ⟨8197067579039692111622309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21858846877439178964326157 8197067579039692111622309)
        ·
          refine ⟨1536950171069942270929183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8197067579039692111622309 1536950171069942270929183)
          ·
            refine ⟨2305425256604913406393775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1536950171069942270929183 2305425256604913406393775)
            ·
              refine ⟨3458137884907370109590663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2305425256604913406393775 3458137884907370109590663)
              ·
                refine ⟨5187206827361055164385995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3458137884907370109590663 5187206827361055164385995)
                ·
                  refine ⟨7780810241041582746578993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5187206827361055164385995 7780810241041582746578993)
                  ·
                    refine ⟨5835607680781187059934245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7780810241041582746578993 5835607680781187059934245)
                    ·
                      refine ⟨1094176440146472573737671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5835607680781187059934245 1094176440146472573737671)
                      ·
                        rfl

theorem cell23_2130901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_2130901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2130901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2130901 prefixEnd_2130901 := by exact prefixLift 2130901
  have htrace : WordTrace (prefixWord ++ tailWord_2130901) baseStart_2130901 baseEnd_2130901 := by
    simpa [prefixWord, tailWord_2130901, baseEnd_2130901] using wordTrace_append hprefix tailTrace_2130901
  have hstable : (prefixWord ++ tailWord_2130901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130901).length < 2 ^ (prefixWord ++ tailWord_2130901).sum := by decide
  have hdescent : baseEnd_2130901 < baseStart_2130901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130904 : List Nat := [2, 1, 2, 2, 2, 5, 1, 1, 1, 3, 3]
def baseStart_2130904 : Nat := 118140960795 + 2130904 * 2 ^ 59
def prefixEnd_2130904 : Nat := 4983230072969 + 3 ^ 40 * 2130904 * 2
def baseEnd_2130904 : Nat := 1094177980588436062000157

theorem tailTrace_2130904 : CollatzResearch.WordTrace tailWord_2130904 prefixEnd_2130904 1094177980588436062000157 := by
  unfold tailWord_2130904
  simp only [CollatzResearch.WordTrace]
  refine ⟨38860226936053106137203883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51813635914737474849605177 38860226936053106137203883)
  ·
    refine ⟨58290340404079659205805825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38860226936053106137203883 58290340404079659205805825)
    ·
      refine ⟨43717755303059744404354369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58290340404079659205805825 43717755303059744404354369)
      ·
        refine ⟨32788316477294808303265777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43717755303059744404354369 32788316477294808303265777)
        ·
          refine ⟨24591237357971106227449333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32788316477294808303265777 24591237357971106227449333)
          ·
            refine ⟨2305428502309791208823375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24591237357971106227449333 2305428502309791208823375)
            ·
              refine ⟨3458142753464686813235063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2305428502309791208823375 3458142753464686813235063)
              ·
                refine ⟨5187214130197030219852595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3458142753464686813235063 5187214130197030219852595)
                ·
                  refine ⟨7780821195295545329778893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5187214130197030219852595 7780821195295545329778893)
                  ·
                    refine ⟨2917807948235829498667085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7780821195295545329778893 2917807948235829498667085)
                    ·
                      refine ⟨1094177980588436062000157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2917807948235829498667085 1094177980588436062000157)
                      ·
                        rfl

theorem cell23_2130904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 1, 3, 3].length) (baseStart_2130904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2130904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2130904 prefixEnd_2130904 := by exact prefixLift 2130904
  have htrace : WordTrace (prefixWord ++ tailWord_2130904) baseStart_2130904 baseEnd_2130904 := by
    simpa [prefixWord, tailWord_2130904, baseEnd_2130904] using wordTrace_append hprefix tailTrace_2130904
  have hstable : (prefixWord ++ tailWord_2130904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130904).length < 2 ^ (prefixWord ++ tailWord_2130904).sum := by decide
  have hdescent : baseEnd_2130904 < baseStart_2130904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130920 : List Nat := [2, 1, 4, 1, 1, 1, 2, 2, 1, 8]
def baseStart_2130920 : Nat := 118140960795 + 2130920 * 2 ^ 59
def prefixEnd_2130920 : Nat := 4983230072969 + 3 ^ 40 * 2130920 * 2
def baseEnd_2130920 : Nat := 364728732092969333133361

theorem tailTrace_2130920 : CollatzResearch.WordTrace tailWord_2130920 prefixEnd_2130920 364728732092969333133361 := by
  unfold tailWord_2130920
  simp only [CollatzResearch.WordTrace]
  refine ⟨38860518720024123503495107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51814024960032164671326809 38860518720024123503495107)
  ·
    refine ⟨58290778080036185255242661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38860518720024123503495107 58290778080036185255242661)
    ·
      refine ⟨10929520890006784735357999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58290778080036185255242661 10929520890006784735357999)
      ·
        refine ⟨16394281335010177103036999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10929520890006784735357999 16394281335010177103036999)
        ·
          refine ⟨24591422002515265654555499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16394281335010177103036999 24591422002515265654555499)
          ·
            refine ⟨36887133003772898481833249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24591422002515265654555499 36887133003772898481833249)
            ·
              refine ⟨27665349752829673861374937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36887133003772898481833249 27665349752829673861374937)
              ·
                refine ⟨20749012314622255396031203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27665349752829673861374937 20749012314622255396031203)
                ·
                  refine ⟨31123518471933383094046805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20749012314622255396031203 31123518471933383094046805)
                  ·
                    refine ⟨364728732092969333133361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 31123518471933383094046805 364728732092969333133361)
                    ·
                      rfl

theorem cell23_2130920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_2130920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2130920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2130920 prefixEnd_2130920 := by exact prefixLift 2130920
  have htrace : WordTrace (prefixWord ++ tailWord_2130920) baseStart_2130920 baseEnd_2130920 := by
    simpa [prefixWord, tailWord_2130920, baseEnd_2130920] using wordTrace_append hprefix tailTrace_2130920
  have hstable : (prefixWord ++ tailWord_2130920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130920).length < 2 ^ (prefixWord ++ tailWord_2130920).sum := by decide
  have hdescent : baseEnd_2130920 < baseStart_2130920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131001 : List Nat := [1, 2, 1, 5, 2, 1, 4, 2, 5]
def baseStart_2131001 : Nat := 118140960795 + 2131001 * 2 ^ 59
def prefixEnd_2131001 : Nat := 4983230072969 + 3 ^ 40 * 2131001 * 2
def baseEnd_2131001 : Nat := 121580865356880242498579

theorem tailTrace_2131001 : CollatzResearch.WordTrace tailWord_2131001 prefixEnd_2131001 121580865356880242498579 := by
  unfold tailWord_2131001
  simp only [CollatzResearch.WordTrace]
  refine ⟨77723991752754797840688857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51815994501836531893792571 77723991752754797840688857)
  ·
    refine ⟨58292993814566098380516643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77723991752754797840688857 58292993814566098380516643)
    ·
      refine ⟨87439490721849147570774965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58292993814566098380516643 87439490721849147570774965)
      ·
        refine ⟨8197452255173357584760153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 87439490721849147570774965 8197452255173357584760153)
        ·
          refine ⟨6148089191380018188570115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8197452255173357584760153 6148089191380018188570115)
          ·
            refine ⟨9222133787070027282855173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6148089191380018188570115 9222133787070027282855173)
            ·
              refine ⟨1729150085075630115535345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9222133787070027282855173 1729150085075630115535345)
              ·
                refine ⟨1296862563806722586651509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1729150085075630115535345 1296862563806722586651509)
                ·
                  refine ⟨121580865356880242498579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1296862563806722586651509 121580865356880242498579)
                  ·
                    rfl

theorem cell23_2131001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 2, 5].length) (baseStart_2131001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2131001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2131001 prefixEnd_2131001 := by exact prefixLift 2131001
  have htrace : WordTrace (prefixWord ++ tailWord_2131001) baseStart_2131001 baseEnd_2131001 := by
    simpa [prefixWord, tailWord_2131001, baseEnd_2131001] using wordTrace_append hprefix tailTrace_2131001
  have hstable : (prefixWord ++ tailWord_2131001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131001).length < 2 ^ (prefixWord ++ tailWord_2131001).sum := by decide
  have hdescent : baseEnd_2131001 < baseStart_2131001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131004 : List Nat := [2, 2, 2, 2, 2, 2, 1, 1, 2, 5, 2]
def baseStart_2131004 : Nat := 118140960795 + 2131004 * 2 ^ 59
def prefixEnd_2131004 : Nat := 4983230072969 + 3 ^ 40 * 2131004 * 2
def baseEnd_2131004 : Nat := 1094229328653885670749697

theorem tailTrace_2131004 : CollatzResearch.WordTrace tailWord_2131004 prefixEnd_2131004 1094229328653885670749697 := by
  unfold tailWord_2131004
  simp only [CollatzResearch.WordTrace]
  refine ⟨38862050585871964676524033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51816067447829286235365377 38862050585871964676524033)
  ·
    refine ⟨29146537939403973507393025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38862050585871964676524033 29146537939403973507393025)
    ·
      refine ⟨21859903454552980130544769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29146537939403973507393025 21859903454552980130544769)
      ·
        refine ⟨16394927590914735097908577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21859903454552980130544769 16394927590914735097908577)
        ·
          refine ⟨12296195693186051323431433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16394927590914735097908577 12296195693186051323431433)
          ·
            refine ⟨9222146769889538492573575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12296195693186051323431433 9222146769889538492573575)
            ·
              refine ⟨13833220154834307738860363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9222146769889538492573575 13833220154834307738860363)
              ·
                refine ⟨20749830232251461608290545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13833220154834307738860363 20749830232251461608290545)
                ·
                  refine ⟨15562372674188596206217909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20749830232251461608290545 15562372674188596206217909)
                  ·
                    refine ⟨1458972438205180894332929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15562372674188596206217909 1458972438205180894332929)
                    ·
                      refine ⟨1094229328653885670749697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1458972438205180894332929 1094229328653885670749697)
                      ·
                        rfl

theorem cell23_2131004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 2, 5, 2].length) (baseStart_2131004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2131004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2131004 prefixEnd_2131004 := by exact prefixLift 2131004
  have htrace : WordTrace (prefixWord ++ tailWord_2131004) baseStart_2131004 baseEnd_2131004 := by
    simpa [prefixWord, tailWord_2131004, baseEnd_2131004] using wordTrace_append hprefix tailTrace_2131004
  have hstable : (prefixWord ++ tailWord_2131004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131004).length < 2 ^ (prefixWord ++ tailWord_2131004).sum := by decide
  have hdescent : baseEnd_2131004 < baseStart_2131004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131027 : List Nat := [1, 1, 1, 2, 1, 1, 2, 5, 5, 4]
def baseStart_2131027 : Nat := 118140960795 + 2131027 * 2 ^ 59
def prefixEnd_2131027 : Nat := 4983230072969 + 3 ^ 40 * 2131027 * 2
def baseEnd_2131027 : Nat := 364747046236313026920697

theorem tailTrace_2131027 : CollatzResearch.WordTrace tailWord_2131027 prefixEnd_2131027 364747046236313026920697 := by
  unfold tailWord_2131027
  simp only [CollatzResearch.WordTrace]
  refine ⟨77724940050660604281135335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51816626700440402854090223 77724940050660604281135335)
  ·
    refine ⟨116587410075990906421703003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77724940050660604281135335 116587410075990906421703003)
    ·
      refine ⟨174881115113986359632554505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116587410075990906421703003 174881115113986359632554505)
      ·
        refine ⟨131160836335489769724415879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174881115113986359632554505 131160836335489769724415879)
        ·
          refine ⟨196741254503234654586623819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131160836335489769724415879 196741254503234654586623819)
          ·
            refine ⟨295111881754851981879935729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196741254503234654586623819 295111881754851981879935729)
            ·
              refine ⟨221333911316138986409951797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 295111881754851981879935729 221333911316138986409951797)
              ·
                refine ⟨20750054185888029975932981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 221333911316138986409951797 20750054185888029975932981)
                ·
                  refine ⟨1945317579927002810243717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20750054185888029975932981 1945317579927002810243717)
                  ·
                    refine ⟨364747046236313026920697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1945317579927002810243717 364747046236313026920697)
                    ·
                      rfl

theorem cell23_2131027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 5, 4].length) (baseStart_2131027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2131027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2131027 prefixEnd_2131027 := by exact prefixLift 2131027
  have htrace : WordTrace (prefixWord ++ tailWord_2131027) baseStart_2131027 baseEnd_2131027 := by
    simpa [prefixWord, tailWord_2131027, baseEnd_2131027] using wordTrace_append hprefix tailTrace_2131027
  have hstable : (prefixWord ++ tailWord_2131027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131027).length < 2 ^ (prefixWord ++ tailWord_2131027).sum := by decide
  have hdescent : baseEnd_2131027 < baseStart_2131027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131047 : List Nat := [1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 6]
def baseStart_2131047 : Nat := 118140960795 + 2131047 * 2 ^ 59
def prefixEnd_2131047 : Nat := 4983230072969 + 3 ^ 40 * 2131047 * 2
def baseEnd_2131047 : Nat := 1094251408322029002511999

theorem tailTrace_2131047 : CollatzResearch.WordTrace tailWord_2131047 prefixEnd_2131047 1094251408322029002511999 := by
  unfold tailWord_2131047
  simp only [CollatzResearch.WordTrace]
  refine ⟨77725669510588147696863395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51817113007058765131242263 77725669510588147696863395)
  ·
    refine ⟨116588504265882221545295093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77725669510588147696863395 116588504265882221545295093)
    ·
      refine ⟨10930172274926458269871415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 116588504265882221545295093 10930172274926458269871415)
      ·
        refine ⟨16395258412389687404807123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10930172274926458269871415 16395258412389687404807123)
        ·
          refine ⟨24592887618584531107210685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16395258412389687404807123 24592887618584531107210685)
          ·
            refine ⟨9222332856969199165204007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24592887618584531107210685 9222332856969199165204007)
            ·
              refine ⟨13833499285453798747806011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9222332856969199165204007 13833499285453798747806011)
              ·
                refine ⟨20750248928180698121709017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13833499285453798747806011 20750248928180698121709017)
                ·
                  refine ⟨15562686696135523591281763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20750248928180698121709017 15562686696135523591281763)
                  ·
                    refine ⟨23344030044203285386922645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15562686696135523591281763 23344030044203285386922645)
                    ·
                      refine ⟨1094251408322029002511999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23344030044203285386922645 1094251408322029002511999)
                      ·
                        rfl

theorem cell23_2131047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_2131047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2131047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2131047 prefixEnd_2131047 := by exact prefixLift 2131047
  have htrace : WordTrace (prefixWord ++ tailWord_2131047) baseStart_2131047 baseEnd_2131047 := by
    simpa [prefixWord, tailWord_2131047, baseEnd_2131047] using wordTrace_append hprefix tailTrace_2131047
  have hstable : (prefixWord ++ tailWord_2131047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131047).length < 2 ^ (prefixWord ++ tailWord_2131047).sum := by decide
  have hdescent : baseEnd_2131047 < baseStart_2131047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131057 : List Nat := [1, 2, 2, 2, 1, 1, 2, 6, 6]
def baseStart_2131057 : Nat := 118140960795 + 2131057 * 2 ^ 59
def prefixEnd_2131057 : Nat := 4983230072969 + 3 ^ 40 * 2131057 * 2
def baseEnd_2131057 : Nat := 121584060347619329265217

theorem tailTrace_2131057 : CollatzResearch.WordTrace tailWord_2131057 prefixEnd_2131057 121584060347619329265217 := by
  unfold tailWord_2131057
  simp only [CollatzResearch.WordTrace]
  refine ⟨77726034240551919404727425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51817356160367946269818283 77726034240551919404727425)
  ·
    refine ⟨58294525680413939553545569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77726034240551919404727425 58294525680413939553545569)
    ·
      refine ⟨43720894260310454665159177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58294525680413939553545569 43720894260310454665159177)
      ·
        refine ⟨32790670695232840998869383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43720894260310454665159177 32790670695232840998869383)
        ·
          refine ⟨49186006042849261498304075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32790670695232840998869383 49186006042849261498304075)
          ·
            refine ⟨73779009064273892247456113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49186006042849261498304075 73779009064273892247456113)
            ·
              refine ⟨55334256798205419185592085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73779009064273892247456113 55334256798205419185592085)
              ·
                refine ⟨2593793287415879024324629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 55334256798205419185592085 2593793287415879024324629)
                ·
                  refine ⟨121584060347619329265217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2593793287415879024324629 121584060347619329265217)
                  ·
                    rfl

theorem cell23_2131057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 6, 6].length) (baseStart_2131057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2131057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2131057 prefixEnd_2131057 := by exact prefixLift 2131057
  have htrace : WordTrace (prefixWord ++ tailWord_2131057) baseStart_2131057 baseEnd_2131057 := by
    simpa [prefixWord, tailWord_2131057, baseEnd_2131057] using wordTrace_append hprefix tailTrace_2131057
  have hstable : (prefixWord ++ tailWord_2131057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131057).length < 2 ^ (prefixWord ++ tailWord_2131057).sum := by decide
  have hdescent : baseEnd_2131057 < baseStart_2131057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131104 : List Nat := [2, 1, 1, 4, 2, 1, 1, 5, 1, 5]
def baseStart_2131104 : Nat := 118140960795 + 2131104 * 2 ^ 59
def prefixEnd_2131104 : Nat := 4983230072969 + 3 ^ 40 * 2131104 * 2
def baseEnd_2131104 : Nat := 364760225573111759833079

theorem tailTrace_2131104 : CollatzResearch.WordTrace tailWord_2131104 prefixEnd_2131104 364760225573111759833079 := by
  unfold tailWord_2131104
  simp only [CollatzResearch.WordTrace]
  refine ⟨38863874235690823215844183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51818498980921097621125577 38863874235690823215844183)
  ·
    refine ⟨58295811353536234823766275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38863874235690823215844183 58295811353536234823766275)
    ·
      refine ⟨87443717030304352235649413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58295811353536234823766275 87443717030304352235649413)
      ·
        refine ⟨16395696943182066044184265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87443717030304352235649413 16395696943182066044184265)
        ·
          refine ⟨12296772707386549533138199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16395696943182066044184265 12296772707386549533138199)
          ·
            refine ⟨18445159061079824299707299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12296772707386549533138199 18445159061079824299707299)
            ·
              refine ⟨27667738591619736449560949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18445159061079824299707299 27667738591619736449560949)
              ·
                refine ⟨2593850492964350292146339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27667738591619736449560949 2593850492964350292146339)
                ·
                  refine ⟨3890775739446525438219509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2593850492964350292146339 3890775739446525438219509)
                  ·
                    refine ⟨364760225573111759833079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3890775739446525438219509 364760225573111759833079)
                    ·
                      rfl

theorem cell23_2131104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 5, 1, 5].length) (baseStart_2131104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2131104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2131104 prefixEnd_2131104 := by exact prefixLift 2131104
  have htrace : WordTrace (prefixWord ++ tailWord_2131104) baseStart_2131104 baseEnd_2131104 := by
    simpa [prefixWord, tailWord_2131104, baseEnd_2131104] using wordTrace_append hprefix tailTrace_2131104
  have hstable : (prefixWord ++ tailWord_2131104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131104).length < 2 ^ (prefixWord ++ tailWord_2131104).sum := by decide
  have hdescent : baseEnd_2131104 < baseStart_2131104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131141 : List Nat := [1, 3, 1, 1, 1, 1, 3, 3, 5, 2, 2]
def baseStart_2131141 : Nat := 118140960795 + 2131141 * 2 ^ 59
def prefixEnd_2131141 : Nat := 4983230072969 + 3 ^ 40 * 2131141 * 2
def baseEnd_2131141 : Nat := 1094299675503551634736567

theorem tailTrace_2131141 : CollatzResearch.WordTrace tailWord_2131141 prefixEnd_2131141 1094299675503551634736567 := by
  unfold tailWord_2131141
  simp only [CollatzResearch.WordTrace]
  refine ⟨77729097972247601750785277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51819398648165067833856851 77729097972247601750785277)
  ·
    refine ⟨29148411739592850656544479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77729097972247601750785277 29148411739592850656544479)
    ·
      refine ⟨43722617609389275984816719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29148411739592850656544479 43722617609389275984816719)
      ·
        refine ⟨65583926414083913977225079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43722617609389275984816719 65583926414083913977225079)
        ·
          refine ⟨98375889621125870965837619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65583926414083913977225079 98375889621125870965837619)
          ·
            refine ⟨147563834431688806448756429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98375889621125870965837619 147563834431688806448756429)
            ·
              refine ⟨55336437911883302418283661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 147563834431688806448756429 55336437911883302418283661)
              ·
                refine ⟨20751164216956238406856373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55336437911883302418283661 20751164216956238406856373)
                ·
                  refine ⟨1945421645339647350642785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20751164216956238406856373 1945421645339647350642785)
                  ·
                    refine ⟨1459066234004735512982089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1945421645339647350642785 1459066234004735512982089)
                    ·
                      refine ⟨1094299675503551634736567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1459066234004735512982089 1094299675503551634736567)
                      ·
                        rfl

theorem cell23_2131141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 5, 2, 2].length) (baseStart_2131141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2131141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2131141 prefixEnd_2131141 := by exact prefixLift 2131141
  have htrace : WordTrace (prefixWord ++ tailWord_2131141) baseStart_2131141 baseEnd_2131141 := by
    simpa [prefixWord, tailWord_2131141, baseEnd_2131141] using wordTrace_append hprefix tailTrace_2131141
  have hstable : (prefixWord ++ tailWord_2131141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131141).length < 2 ^ (prefixWord ++ tailWord_2131141).sum := by decide
  have hdescent : baseEnd_2131141 < baseStart_2131141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131181 : List Nat := [1, 5, 1, 2, 2, 3, 1, 8]
def baseStart_2131181 : Nat := 118140960795 + 2131181 * 2 ^ 59
def prefixEnd_2131181 : Nat := 4983230072969 + 3 ^ 40 * 2131181 * 2
def baseEnd_2131181 : Nat := 40530378323323388082829

theorem tailTrace_2131181 : CollatzResearch.WordTrace tailWord_2131181 prefixEnd_2131181 40530378323323388082829 := by
  unfold tailWord_2131181
  simp only [CollatzResearch.WordTrace]
  refine ⟨77730556892102688582241397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51820371261401792388160931 77730556892102688582241397)
  ·
    refine ⟨7287239708634627054585131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77730556892102688582241397 7287239708634627054585131)
    ·
      refine ⟨10930859562951940581877697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7287239708634627054585131 10930859562951940581877697)
      ·
        refine ⟨8198144672213955436408273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10930859562951940581877697 8198144672213955436408273)
        ·
          refine ⟨6148608504160466577306205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8198144672213955436408273 6148608504160466577306205)
          ·
            refine ⟨2305728189060174966489827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6148608504160466577306205 2305728189060174966489827)
            ·
              refine ⟨3458592283590262449734741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2305728189060174966489827 3458592283590262449734741)
              ·
                refine ⟨40530378323323388082829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3458592283590262449734741 40530378323323388082829)
                ·
                  rfl

theorem cell23_2131181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 8].length) (baseStart_2131181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2131181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2131181 prefixEnd_2131181 := by exact prefixLift 2131181
  have htrace : WordTrace (prefixWord ++ tailWord_2131181) baseStart_2131181 baseEnd_2131181 := by
    simpa [prefixWord, tailWord_2131181, baseEnd_2131181] using wordTrace_append hprefix tailTrace_2131181
  have hstable : (prefixWord ++ tailWord_2131181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131181).length < 2 ^ (prefixWord ++ tailWord_2131181).sum := by decide
  have hdescent : baseEnd_2131181 < baseStart_2131181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131224 : List Nat := [2, 1, 2, 3, 1, 3, 1, 2, 2, 6]
def baseStart_2131224 : Nat := 118140960795 + 2131224 * 2 ^ 59
def prefixEnd_2131224 : Nat := 4983230072969 + 3 ^ 40 * 2131224 * 2
def baseEnd_2131224 : Nat := 364780764799291603332895

theorem tailTrace_2131224 : CollatzResearch.WordTrace tailWord_2131224 prefixEnd_2131224 364780764799291603332895 := by
  unfold tailWord_2131224
  simp only [CollatzResearch.WordTrace]
  refine ⟨38866062615473453463028363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51821416820631271284037817 38866062615473453463028363)
  ·
    refine ⟨58299093923210180194542545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38866062615473453463028363 58299093923210180194542545)
    ·
      refine ⟨43724320442407635145906909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58299093923210180194542545 43724320442407635145906909)
      ·
        refine ⟨16396620165902863179715091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43724320442407635145906909 16396620165902863179715091)
        ·
          refine ⟨24594930248854294769572637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16396620165902863179715091 24594930248854294769572637)
          ·
            refine ⟨9223098843320360538589739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24594930248854294769572637 9223098843320360538589739)
            ·
              refine ⟨13834648264980540807884609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9223098843320360538589739 13834648264980540807884609)
              ·
                refine ⟨10375986198735405605913457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13834648264980540807884609 10375986198735405605913457)
                ·
                  refine ⟨7781989649051554204435093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10375986198735405605913457 7781989649051554204435093)
                  ·
                    refine ⟨364780764799291603332895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7781989649051554204435093 364780764799291603332895)
                    ·
                      rfl

theorem cell23_2131224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 2, 6].length) (baseStart_2131224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2131224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2131224 prefixEnd_2131224 := by exact prefixLift 2131224
  have htrace : WordTrace (prefixWord ++ tailWord_2131224) baseStart_2131224 baseEnd_2131224 := by
    simpa [prefixWord, tailWord_2131224, baseEnd_2131224] using wordTrace_append hprefix tailTrace_2131224
  have hstable : (prefixWord ++ tailWord_2131224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131224).length < 2 ^ (prefixWord ++ tailWord_2131224).sum := by decide
  have hdescent : baseEnd_2131224 < baseStart_2131224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131242 : List Nat := [3, 1, 4, 2, 1, 2, 3, 1, 2, 1, 3]
def baseStart_2131242 : Nat := 118140960795 + 2131242 * 2 ^ 59
def prefixEnd_2131242 : Nat := 4983230072969 + 3 ^ 40 * 2131242 * 2
def baseEnd_2131242 : Nat := 1094351537049655739573603

theorem tailTrace_2131242 : CollatzResearch.WordTrace tailWord_2131242 prefixEnd_2131242 1094351537049655739573603 := by
  unfold tailWord_2131242
  simp only [CollatzResearch.WordTrace]
  refine ⟨19433195436220424000052995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51821854496587797333474653 19433195436220424000052995)
  ·
    refine ⟨29149793154330636000079493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19433195436220424000052995 29149793154330636000079493)
    ·
      refine ⟨5465586216436994250014905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29149793154330636000079493 5465586216436994250014905)
      ·
        refine ⟨4099189662327745687511179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5465586216436994250014905 4099189662327745687511179)
        ·
          refine ⟨6148784493491618531266769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4099189662327745687511179 6148784493491618531266769)
          ·
            refine ⟨4611588370118713898450077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6148784493491618531266769 4611588370118713898450077)
            ·
              refine ⟨1729345638794517711918779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4611588370118713898450077 1729345638794517711918779)
              ·
                refine ⟨2594018458191776567878169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1729345638794517711918779 2594018458191776567878169)
                ·
                  refine ⟨1945513843643832425908627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2594018458191776567878169 1945513843643832425908627)
                  ·
                    refine ⟨2918270765465748638862941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1945513843643832425908627 2918270765465748638862941)
                    ·
                      refine ⟨1094351537049655739573603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2918270765465748638862941 1094351537049655739573603)
                      ·
                        rfl

theorem cell23_2131242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_2131242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2131242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2131242 prefixEnd_2131242 := by exact prefixLift 2131242
  have htrace : WordTrace (prefixWord ++ tailWord_2131242) baseStart_2131242 baseEnd_2131242 := by
    simpa [prefixWord, tailWord_2131242, baseEnd_2131242] using wordTrace_append hprefix tailTrace_2131242
  have hstable : (prefixWord ++ tailWord_2131242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131242).length < 2 ^ (prefixWord ++ tailWord_2131242).sum := by decide
  have hdescent : baseEnd_2131242 < baseStart_2131242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131265 : List Nat := [1, 2, 5, 2, 1, 1, 1, 2, 4, 2, 2]
def baseStart_2131265 : Nat := 118140960795 + 2131265 * 2 ^ 59
def prefixEnd_2131265 : Nat := 4983230072969 + 3 ^ 40 * 2131265 * 2
def baseEnd_2131265 : Nat := 1094363347104709149585997

theorem tailTrace_2131265 : CollatzResearch.WordTrace tailWord_2131265 prefixEnd_2131265 1094363347104709149585997 := by
  unfold tailWord_2131265
  simp only [CollatzResearch.WordTrace]
  refine ⟨77733620623798370928299249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51822413749198913952199499 77733620623798370928299249)
  ·
    refine ⟨58300215467848778196224437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77733620623798370928299249 58300215467848778196224437)
    ·
      refine ⟨5465645200110822955896041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58300215467848778196224437 5465645200110822955896041)
      ·
        refine ⟨4099233900083117216922031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5465645200110822955896041 4099233900083117216922031)
        ·
          refine ⟨6148850850124675825383047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4099233900083117216922031 6148850850124675825383047)
          ·
            refine ⟨9223276275187013738074571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6148850850124675825383047 9223276275187013738074571)
            ·
              refine ⟨13834914412780520607111857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9223276275187013738074571 13834914412780520607111857)
              ·
                refine ⟨10376185809585390455333893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13834914412780520607111857 10376185809585390455333893)
                ·
                  refine ⟨1945534839297260710375105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10376185809585390455333893 1945534839297260710375105)
                  ·
                    refine ⟨1459151129472945532781329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1945534839297260710375105 1459151129472945532781329)
                    ·
                      refine ⟨1094363347104709149585997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1459151129472945532781329 1094363347104709149585997)
                      ·
                        rfl

theorem cell23_2131265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_2131265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2131265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2131265 prefixEnd_2131265 := by exact prefixLift 2131265
  have htrace : WordTrace (prefixWord ++ tailWord_2131265) baseStart_2131265 baseEnd_2131265 := by
    simpa [prefixWord, tailWord_2131265, baseEnd_2131265] using wordTrace_append hprefix tailTrace_2131265
  have hstable : (prefixWord ++ tailWord_2131265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131265).length < 2 ^ (prefixWord ++ tailWord_2131265).sum := by decide
  have hdescent : baseEnd_2131265 < baseStart_2131265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131268 : List Nat := [2, 3, 4, 1, 1, 2, 1, 1, 2, 1, 5]
def baseStart_2131268 : Nat := 118140960795 + 2131268 * 2 ^ 59
def prefixEnd_2131268 : Nat := 4983230072969 + 3 ^ 40 * 2131268 * 2
def baseEnd_2131268 : Nat := 1094364887546672637848483

theorem tailTrace_2131268 : CollatzResearch.WordTrace tailWord_2131268 prefixEnd_2131268 1094364887546672637848483 := by
  unfold tailWord_2131268
  simp only [CollatzResearch.WordTrace]
  refine ⟨38866865021393751220329229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51822486695191668293772305 38866865021393751220329229)
  ·
    refine ⟨14575074383022656707623461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38866865021393751220329229 14575074383022656707623461)
    ·
      refine ⟨2732826446816748132679399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14575074383022656707623461 2732826446816748132679399)
      ·
        refine ⟨4099239670225122199019099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2732826446816748132679399 4099239670225122199019099)
        ·
          refine ⟨6148859505337683298528649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4099239670225122199019099 6148859505337683298528649)
          ·
            refine ⟨4611644629003262473896487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6148859505337683298528649 4611644629003262473896487)
            ·
              refine ⟨6917466943504893710844731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4611644629003262473896487 6917466943504893710844731)
              ·
                refine ⟨10376200415257340566267097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6917466943504893710844731 10376200415257340566267097)
                ·
                  refine ⟨7782150311443005424700323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10376200415257340566267097 7782150311443005424700323)
                  ·
                    refine ⟨11673225467164508137050485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7782150311443005424700323 11673225467164508137050485)
                    ·
                      refine ⟨1094364887546672637848483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11673225467164508137050485 1094364887546672637848483)
                      ·
                        rfl

theorem cell23_2131268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_2131268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2131268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2131268 prefixEnd_2131268 := by exact prefixLift 2131268
  have htrace : WordTrace (prefixWord ++ tailWord_2131268) baseStart_2131268 baseEnd_2131268 := by
    simpa [prefixWord, tailWord_2131268, baseEnd_2131268] using wordTrace_append hprefix tailTrace_2131268
  have hstable : (prefixWord ++ tailWord_2131268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131268).length < 2 ^ (prefixWord ++ tailWord_2131268).sum := by decide
  have hdescent : baseEnd_2131268 < baseStart_2131268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131288 : List Nat := [2, 1, 2, 2, 1, 1, 7, 2, 5]
def baseStart_2131288 : Nat := 118140960795 + 2131288 * 2 ^ 59
def prefixEnd_2131288 : Nat := 4983230072969 + 3 ^ 40 * 2131288 * 2
def baseEnd_2131288 : Nat := 121597239684418062177599

theorem tailTrace_2131288 : CollatzResearch.WordTrace tailWord_2131288 prefixEnd_2131288 121597239684418062177599 := by
  unfold tailWord_2131288
  simp only [CollatzResearch.WordTrace]
  refine ⟨38867229751357522928193259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51822973001810030570924345 38867229751357522928193259)
  ·
    refine ⟨58300844627036284392289889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38867229751357522928193259 58300844627036284392289889)
    ·
      refine ⟨43725633470277213294217417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58300844627036284392289889 43725633470277213294217417)
      ·
        refine ⟨32794225102707909970663063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43725633470277213294217417 32794225102707909970663063)
        ·
          refine ⟨49191337654061864955994595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32794225102707909970663063 49191337654061864955994595)
          ·
            refine ⟨73787006481092797433991893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49191337654061864955994595 73787006481092797433991893)
            ·
              refine ⟨1729382964400612439859185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 73787006481092797433991893 1729382964400612439859185)
              ·
                refine ⟨1297037223300459329894389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1729382964400612439859185 1297037223300459329894389)
                ·
                  refine ⟨121597239684418062177599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1297037223300459329894389 121597239684418062177599)
                  ·
                    rfl

theorem cell23_2131288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 2, 5].length) (baseStart_2131288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2131288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2131288 prefixEnd_2131288 := by exact prefixLift 2131288
  have htrace : WordTrace (prefixWord ++ tailWord_2131288) baseStart_2131288 baseEnd_2131288 := by
    simpa [prefixWord, tailWord_2131288, baseEnd_2131288] using wordTrace_append hprefix tailTrace_2131288
  have hstable : (prefixWord ++ tailWord_2131288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131288).length < 2 ^ (prefixWord ++ tailWord_2131288).sum := by decide
  have hdescent : baseEnd_2131288 < baseStart_2131288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131293 : List Nat := [1, 4, 5, 1, 2, 1, 2, 1, 2, 1, 3]
def baseStart_2131293 : Nat := 118140960795 + 2131293 * 2 ^ 59
def prefixEnd_2131293 : Nat := 4983230072969 + 3 ^ 40 * 2131293 * 2
def baseEnd_2131293 : Nat := 1094377724563035040035869

theorem tailTrace_2131293 : CollatzResearch.WordTrace tailWord_2131293 prefixEnd_2131293 1094377724563035040035869 := by
  unfold tailWord_2131293
  simp only [CollatzResearch.WordTrace]
  refine ⟨77734641867696931710318533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51823094578464621140212355 77734641867696931710318533)
  ·
    refine ⟨14575245350193174695684725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77734641867696931710318533 14575245350193174695684725)
    ·
      refine ⟨1366429251580610127720443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14575245350193174695684725 1366429251580610127720443)
      ·
        refine ⟨2049643877370915191580665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1366429251580610127720443 2049643877370915191580665)
        ·
          refine ⟨1537232908028186393685499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2049643877370915191580665 1537232908028186393685499)
          ·
            refine ⟨2305849362042279590528249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1537232908028186393685499 2305849362042279590528249)
            ·
              refine ⟨1729387021531709692896187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2305849362042279590528249 1729387021531709692896187)
              ·
                refine ⟨2594080532297564539344281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1729387021531709692896187 2594080532297564539344281)
                ·
                  refine ⟨1945560399223173404508211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2594080532297564539344281 1945560399223173404508211)
                  ·
                    refine ⟨2918340598834760106762317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1945560399223173404508211 2918340598834760106762317)
                    ·
                      refine ⟨1094377724563035040035869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2918340598834760106762317 1094377724563035040035869)
                      ·
                        rfl

theorem cell23_2131293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_2131293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2131293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2131293 prefixEnd_2131293 := by exact prefixLift 2131293
  have htrace : WordTrace (prefixWord ++ tailWord_2131293) baseStart_2131293 baseEnd_2131293 := by
    simpa [prefixWord, tailWord_2131293, baseEnd_2131293] using wordTrace_append hprefix tailTrace_2131293
  have hstable : (prefixWord ++ tailWord_2131293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131293).length < 2 ^ (prefixWord ++ tailWord_2131293).sum := by decide
  have hdescent : baseEnd_2131293 < baseStart_2131293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131321 : List Nat := [1, 2, 1, 3, 2, 1, 3, 3, 2, 1, 4]
def baseStart_2131321 : Nat := 118140960795 + 2131321 * 2 ^ 59
def prefixEnd_2131321 : Nat := 4983230072969 + 3 ^ 40 * 2131321 * 2
def baseEnd_2131321 : Nat := 1094392102021360930485739

theorem tailTrace_2131321 : CollatzResearch.WordTrace tailWord_2131321 prefixEnd_2131321 1094392102021360930485739 := by
  unfold tailWord_2131321
  simp only [CollatzResearch.WordTrace]
  refine ⟨77735663111595492492337817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51823775407730328328225211 77735663111595492492337817)
  ·
    refine ⟨58301747333696619369253363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77735663111595492492337817 58301747333696619369253363)
    ·
      refine ⟨87452621000544929053880045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58301747333696619369253363 87452621000544929053880045)
      ·
        refine ⟨32794732875204348395205017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87452621000544929053880045 32794732875204348395205017)
        ·
          refine ⟨24596049656403261296403763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32794732875204348395205017 24596049656403261296403763)
          ·
            refine ⟨36894074484604891944605645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24596049656403261296403763 36894074484604891944605645)
            ·
              refine ⟨13835277931726834479227117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36894074484604891944605645 13835277931726834479227117)
              ·
                refine ⟨5188229224397562929710169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13835277931726834479227117 5188229224397562929710169)
                ·
                  refine ⟨3891171918298172197282627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5188229224397562929710169 3891171918298172197282627)
                  ·
                    refine ⟨5836757877447258295923941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3891171918298172197282627 5836757877447258295923941)
                    ·
                      refine ⟨1094392102021360930485739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5836757877447258295923941 1094392102021360930485739)
                      ·
                        rfl

theorem cell23_2131321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_2131321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2131321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2131321 prefixEnd_2131321 := by exact prefixLift 2131321
  have htrace : WordTrace (prefixWord ++ tailWord_2131321) baseStart_2131321 baseEnd_2131321 := by
    simpa [prefixWord, tailWord_2131321, baseEnd_2131321] using wordTrace_append hprefix tailTrace_2131321
  have hstable : (prefixWord ++ tailWord_2131321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131321).length < 2 ^ (prefixWord ++ tailWord_2131321).sum := by decide
  have hdescent : baseEnd_2131321 < baseStart_2131321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131438 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 6, 4]
def baseStart_2131438 : Nat := 118140960795 + 2131438 * 2 ^ 59
def prefixEnd_2131438 : Nat := 4983230072969 + 3 ^ 40 * 2131438 * 2
def baseEnd_2131438 : Nat := 364817393085978990907567

theorem tailTrace_2131438 : CollatzResearch.WordTrace tailWord_2131438 prefixEnd_2131438 364817393085978990907567 := by
  unfold tailWord_2131438
  simp only [CollatzResearch.WordTrace]
  refine ⟨9717491306521452684293371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51826620301447747649564645 9717491306521452684293371)
  ·
    refine ⟨14576236959782179026440057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9717491306521452684293371 14576236959782179026440057)
    ·
      refine ⟨10932177719836634269830043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14576236959782179026440057 10932177719836634269830043)
      ·
        refine ⟨16398266579754951404745065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10932177719836634269830043 16398266579754951404745065)
        ·
          refine ⟨12298699934816213553558799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16398266579754951404745065 12298699934816213553558799)
          ·
            refine ⟨18448049902224320330338199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12298699934816213553558799 18448049902224320330338199)
            ·
              refine ⟨27672074853336480495507299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18448049902224320330338199 27672074853336480495507299)
              ·
                refine ⟨41508112280004720743260949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27672074853336480495507299 41508112280004720743260949)
                ·
                  refine ⟨1945692763125221284840357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 41508112280004720743260949 1945692763125221284840357)
                  ·
                    refine ⟨364817393085978990907567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1945692763125221284840357 364817393085978990907567)
                    ·
                      rfl

theorem cell23_2131438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_2131438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2131438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2131438 prefixEnd_2131438 := by exact prefixLift 2131438
  have htrace : WordTrace (prefixWord ++ tailWord_2131438) baseStart_2131438 baseEnd_2131438 := by
    simpa [prefixWord, tailWord_2131438, baseEnd_2131438] using wordTrace_append hprefix tailTrace_2131438
  have hstable : (prefixWord ++ tailWord_2131438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131438).length < 2 ^ (prefixWord ++ tailWord_2131438).sum := by decide
  have hdescent : baseEnd_2131438 < baseStart_2131438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131448 : List Nat := [2, 1, 2, 1, 1, 6, 2, 1, 1, 1, 5]
def baseStart_2131448 : Nat := 118140960795 + 2131448 * 2 ^ 59
def prefixEnd_2131448 : Nat := 4983230072969 + 3 ^ 40 * 2131448 * 2
def baseEnd_2131448 : Nat := 1094457314064481933597655

theorem tailTrace_2131448 : CollatzResearch.WordTrace tailWord_2131448 prefixEnd_2131448 1094457314064481933597655 := by
  unfold tailWord_2131448
  simp only [CollatzResearch.WordTrace]
  refine ⟨38870147591067696591105499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51826863454756928788140665 38870147591067696591105499)
  ·
    refine ⟨58305221386601544886658249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38870147591067696591105499 58305221386601544886658249)
    ·
      refine ⟨43728916039951158664993687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58305221386601544886658249 43728916039951158664993687)
      ·
        refine ⟨65593374059926737997490531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43728916039951158664993687 65593374059926737997490531)
        ·
          refine ⟨98390061089890106996235797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65593374059926737997490531 98390061089890106996235797)
          ·
            refine ⟨4612034113588598765448553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 98390061089890106996235797 4612034113588598765448553)
            ·
              refine ⟨3459025585191449074086415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4612034113588598765448553 3459025585191449074086415)
              ·
                refine ⟨5188538377787173611129623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3459025585191449074086415 5188538377787173611129623)
                ·
                  refine ⟨7782807566680760416694435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5188538377787173611129623 7782807566680760416694435)
                  ·
                    refine ⟨11674211350021140625041653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7782807566680760416694435 11674211350021140625041653)
                    ·
                      refine ⟨1094457314064481933597655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11674211350021140625041653 1094457314064481933597655)
                      ·
                        rfl

theorem cell23_2131448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 1, 1, 5].length) (baseStart_2131448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2131448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2131448 prefixEnd_2131448 := by exact prefixLift 2131448
  have htrace : WordTrace (prefixWord ++ tailWord_2131448) baseStart_2131448 baseEnd_2131448 := by
    simpa [prefixWord, tailWord_2131448, baseEnd_2131448] using wordTrace_append hprefix tailTrace_2131448
  have hstable : (prefixWord ++ tailWord_2131448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131448).length < 2 ^ (prefixWord ++ tailWord_2131448).sum := by decide
  have hdescent : baseEnd_2131448 < baseStart_2131448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131468 : List Nat := [2, 2, 1, 2, 5, 1, 2, 8]
def baseStart_2131468 : Nat := 118140960795 + 2131468 * 2 ^ 59
def prefixEnd_2131468 : Nat := 4983230072969 + 3 ^ 40 * 2131468 * 2
def baseEnd_2131468 : Nat := 40535836432502661309169

theorem tailTrace_2131468 : CollatzResearch.WordTrace tailWord_2131468 prefixEnd_2131468 40535836432502661309169 := by
  unfold tailWord_2131468
  simp only [CollatzResearch.WordTrace]
  refine ⟨38870512321031468298969529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51827349761375291065292705 38870512321031468298969529)
  ·
    refine ⟨29152884240773601224227147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38870512321031468298969529 29152884240773601224227147)
    ·
      refine ⟨43729326361160401836340721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29152884240773601224227147 43729326361160401836340721)
      ·
        refine ⟨32796994770870301377255541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43729326361160401836340721 32796994770870301377255541)
        ·
          refine ⟨3074718259769090754117707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32796994770870301377255541 3074718259769090754117707)
          ·
            refine ⟨4612077389653636131176561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3074718259769090754117707 4612077389653636131176561)
            ·
              refine ⟨3459058042240227098382421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4612077389653636131176561 3459058042240227098382421)
              ·
                refine ⟨40535836432502661309169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3459058042240227098382421 40535836432502661309169)
                ·
                  rfl

theorem cell23_2131468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 8].length) (baseStart_2131468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2131468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2131468 prefixEnd_2131468 := by exact prefixLift 2131468
  have htrace : WordTrace (prefixWord ++ tailWord_2131468) baseStart_2131468 baseEnd_2131468 := by
    simpa [prefixWord, tailWord_2131468, baseEnd_2131468] using wordTrace_append hprefix tailTrace_2131468
  have hstable : (prefixWord ++ tailWord_2131468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131468).length < 2 ^ (prefixWord ++ tailWord_2131468).sum := by decide
  have hdescent : baseEnd_2131468 < baseStart_2131468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131512 : List Nat := [2, 1, 2, 1, 4, 3, 2, 2, 2, 1, 3]
def baseStart_2131512 : Nat := 118140960795 + 2131512 * 2 ^ 59
def prefixEnd_2131512 : Nat := 4983230072969 + 3 ^ 40 * 2131512 * 2
def baseEnd_2131512 : Nat := 1094490176826369683197361

theorem tailTrace_2131512 : CollatzResearch.WordTrace tailWord_2131512 prefixEnd_2131512 1094490176826369683197361 := by
  unfold tailWord_2131512
  simp only [CollatzResearch.WordTrace]
  refine ⟨38871314726951766056270395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51828419635935688075027193 38871314726951766056270395)
  ·
    refine ⟨58306972090427649084405593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38871314726951766056270395 58306972090427649084405593)
    ·
      refine ⟨43730229067820736813304195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58306972090427649084405593 43730229067820736813304195)
      ·
        refine ⟨65595343601731105219956293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43730229067820736813304195 65595343601731105219956293)
        ·
          refine ⟨12299126925324582228741805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65595343601731105219956293 12299126925324582228741805)
          ·
            refine ⟨4612172596996718335778177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12299126925324582228741805 4612172596996718335778177)
            ·
              refine ⟨3459129447747538751833633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4612172596996718335778177 3459129447747538751833633)
              ·
                refine ⟨2594347085810654063875225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3459129447747538751833633 2594347085810654063875225)
                ·
                  refine ⟨1945760314357990547906419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2594347085810654063875225 1945760314357990547906419)
                  ·
                    refine ⟨2918640471536985821859629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1945760314357990547906419 2918640471536985821859629)
                    ·
                      refine ⟨1094490176826369683197361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2918640471536985821859629 1094490176826369683197361)
                      ·
                        rfl

theorem cell23_2131512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 2, 2, 1, 3].length) (baseStart_2131512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2131512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2131512 prefixEnd_2131512 := by exact prefixLift 2131512
  have htrace : WordTrace (prefixWord ++ tailWord_2131512) baseStart_2131512 baseEnd_2131512 := by
    simpa [prefixWord, tailWord_2131512, baseEnd_2131512] using wordTrace_append hprefix tailTrace_2131512
  have hstable : (prefixWord ++ tailWord_2131512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131512).length < 2 ^ (prefixWord ++ tailWord_2131512).sum := by decide
  have hdescent : baseEnd_2131512 < baseStart_2131512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131535 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 6, 2, 2]
def baseStart_2131535 : Nat := 118140960795 + 2131535 * 2 ^ 59
def prefixEnd_2131535 : Nat := 4983230072969 + 3 ^ 40 * 2131535 * 2
def baseEnd_2131535 : Nat := 1094501986881423093209755

theorem tailTrace_2131535 : CollatzResearch.WordTrace tailWord_2131535 prefixEnd_2131535 1094501986881423093209755 := by
  unfold tailWord_2131535
  simp only [CollatzResearch.WordTrace]
  refine ⟨77743468332820207040628059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51828978888546804693752039 77743468332820207040628059)
  ·
    refine ⟨116615202499230310560942089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77743468332820207040628059 116615202499230310560942089)
    ·
      refine ⟨87461401874422732920706567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116615202499230310560942089 87461401874422732920706567)
      ·
        refine ⟨131192102811634099381059851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87461401874422732920706567 131192102811634099381059851)
        ·
          refine ⟨196788154217451149071589777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131192102811634099381059851 196788154217451149071589777)
          ·
            refine ⟨147591115663088361803692333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196788154217451149071589777 147591115663088361803692333)
            ·
              refine ⟨55346668373658135676384625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 147591115663088361803692333 55346668373658135676384625)
              ·
                refine ⟨41510001280243601757288469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55346668373658135676384625 41510001280243601757288469)
                ·
                  refine ⟨1945781310011418832372897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 41510001280243601757288469 1945781310011418832372897)
                  ·
                    refine ⟨1459335982508564124279673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1945781310011418832372897 1459335982508564124279673)
                    ·
                      refine ⟨1094501986881423093209755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1459335982508564124279673 1094501986881423093209755)
                      ·
                        rfl

theorem cell23_2131535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 6, 2, 2].length) (baseStart_2131535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2131535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2131535 prefixEnd_2131535 := by exact prefixLift 2131535
  have htrace : WordTrace (prefixWord ++ tailWord_2131535) baseStart_2131535 baseEnd_2131535 := by
    simpa [prefixWord, tailWord_2131535, baseEnd_2131535] using wordTrace_append hprefix tailTrace_2131535
  have hstable : (prefixWord ++ tailWord_2131535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131535).length < 2 ^ (prefixWord ++ tailWord_2131535).sum := by decide
  have hdescent : baseEnd_2131535 < baseStart_2131535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131551 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 7]
def baseStart_2131551 : Nat := 118140960795 + 2131551 * 2 ^ 59
def prefixEnd_2131551 : Nat := 4983230072969 + 3 ^ 40 * 2131551 * 2
def baseEnd_2131551 : Nat := 1094510202571895030609681

theorem tailTrace_2131551 : CollatzResearch.WordTrace tailWord_2131551 prefixEnd_2131551 1094510202571895030609681 := by
  unfold tailWord_2131551
  simp only [CollatzResearch.WordTrace]
  refine ⟨77744051900762241773210507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51829367933841494515473671 77744051900762241773210507)
  ·
    refine ⟨116616077851143362659815761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77744051900762241773210507 116616077851143362659815761)
    ·
      refine ⟨87462058388357521994861821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116616077851143362659815761 87462058388357521994861821)
      ·
        refine ⟨32798271895634070748073183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87462058388357521994861821 32798271895634070748073183)
        ·
          refine ⟨49197407843451106122109775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32798271895634070748073183 49197407843451106122109775)
          ·
            refine ⟨73796111765176659183164663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49197407843451106122109775 73796111765176659183164663)
            ·
              refine ⟨110694167647764988774746995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73796111765176659183164663 110694167647764988774746995)
              ·
                refine ⟨166041251471647483162120493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110694167647764988774746995 166041251471647483162120493)
                ·
                  refine ⟨62265469301867806185795185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 166041251471647483162120493 62265469301867806185795185)
                  ·
                    refine ⟨46699101976400854639346389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 62265469301867806185795185 46699101976400854639346389)
                    ·
                      refine ⟨1094510202571895030609681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 46699101976400854639346389 1094510202571895030609681)
                      ·
                        rfl

theorem cell23_2131551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_2131551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2131551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2131551 prefixEnd_2131551 := by exact prefixLift 2131551
  have htrace : WordTrace (prefixWord ++ tailWord_2131551) baseStart_2131551 baseEnd_2131551 := by
    simpa [prefixWord, tailWord_2131551, baseEnd_2131551] using wordTrace_append hprefix tailTrace_2131551
  have hstable : (prefixWord ++ tailWord_2131551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131551).length < 2 ^ (prefixWord ++ tailWord_2131551).sum := by decide
  have hdescent : baseEnd_2131551 < baseStart_2131551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131585 : List Nat := [1, 2, 4, 2, 1, 2, 2, 1, 2, 3, 3]
def baseStart_2131585 : Nat := 118140960795 + 2131585 * 2 ^ 59
def prefixEnd_2131585 : Nat := 4983230072969 + 3 ^ 40 * 2131585 * 2
def baseEnd_2131585 : Nat := 1094527660914147897584525

theorem tailTrace_2131585 : CollatzResearch.WordTrace tailWord_2131585 prefixEnd_2131585 1094527660914147897584525 := by
  unfold tailWord_2131585
  simp only [CollatzResearch.WordTrace]
  refine ⟨77745291982639065579948209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51830194655092710386632139 77745291982639065579948209)
  ·
    refine ⟨58308968986979299184961157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77745291982639065579948209 58308968986979299184961157)
    ·
      refine ⟨10932931685058618597180217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58308968986979299184961157 10932931685058618597180217)
      ·
        refine ⟨8199698763793963947885163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10932931685058618597180217 8199698763793963947885163)
        ·
          refine ⟨12299548145690945921827745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8199698763793963947885163 12299548145690945921827745)
          ·
            refine ⟨9224661109268209441370809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12299548145690945921827745 9224661109268209441370809)
            ·
              refine ⟨6918495831951157081028107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9224661109268209441370809 6918495831951157081028107)
              ·
                refine ⟨10377743747926735621542161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6918495831951157081028107 10377743747926735621542161)
                ·
                  refine ⟨7783307810945051716156621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10377743747926735621542161 7783307810945051716156621)
                  ·
                    refine ⟨2918740429104394393558733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7783307810945051716156621 2918740429104394393558733)
                    ·
                      refine ⟨1094527660914147897584525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2918740429104394393558733 1094527660914147897584525)
                      ·
                        rfl

theorem cell23_2131585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_2131585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2131585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2131585 prefixEnd_2131585 := by exact prefixLift 2131585
  have htrace : WordTrace (prefixWord ++ tailWord_2131585) baseStart_2131585 baseEnd_2131585 := by
    simpa [prefixWord, tailWord_2131585, baseEnd_2131585] using wordTrace_append hprefix tailTrace_2131585
  have hstable : (prefixWord ++ tailWord_2131585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131585).length < 2 ^ (prefixWord ++ tailWord_2131585).sum := by decide
  have hdescent : baseEnd_2131585 < baseStart_2131585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131628 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 3]
def baseStart_2131628 : Nat := 118140960795 + 2131628 * 2 ^ 59
def prefixEnd_2131628 : Nat := 4983230072969 + 3 ^ 40 * 2131628 * 2
def baseEnd_2131628 : Nat := 1094549740582291229346827

theorem tailTrace_2131628 : CollatzResearch.WordTrace tailWord_2131628 prefixEnd_2131628 1094549740582291229346827 := by
  unfold tailWord_2131628
  simp only [CollatzResearch.WordTrace]
  refine ⟨38873430160741641961881769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51831240214322189282509025 38873430160741641961881769)
  ·
    refine ⟨29155072620556231471411327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38873430160741641961881769 29155072620556231471411327)
    ·
      refine ⟨43732608930834347207116991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29155072620556231471411327 43732608930834347207116991)
      ·
        refine ⟨65598913396251520810675487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43732608930834347207116991 65598913396251520810675487)
        ·
          refine ⟨98398370094377281216013231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65598913396251520810675487 98398370094377281216013231)
          ·
            refine ⟨147597555141565921824019847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98398370094377281216013231 147597555141565921824019847)
            ·
              refine ⟨221396332712348882736029771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147597555141565921824019847 221396332712348882736029771)
              ·
                refine ⟨332094499068523324104044657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 221396332712348882736029771 332094499068523324104044657)
                ·
                  refine ⟨249070874301392493078033493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 332094499068523324104044657 249070874301392493078033493)
                  ·
                    refine ⟨2918799308219443278258205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 249070874301392493078033493 2918799308219443278258205)
                    ·
                      refine ⟨1094549740582291229346827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2918799308219443278258205 1094549740582291229346827)
                      ·
                        rfl

theorem cell23_2131628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 3].length) (baseStart_2131628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2131628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2131628 prefixEnd_2131628 := by exact prefixLift 2131628
  have htrace : WordTrace (prefixWord ++ tailWord_2131628) baseStart_2131628 baseEnd_2131628 := by
    simpa [prefixWord, tailWord_2131628, baseEnd_2131628] using wordTrace_append hprefix tailTrace_2131628
  have hstable : (prefixWord ++ tailWord_2131628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131628).length < 2 ^ (prefixWord ++ tailWord_2131628).sum := by decide
  have hdescent : baseEnd_2131628 < baseStart_2131628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131645 : List Nat := [1, 4, 1, 2, 1, 2, 1, 2, 4, 2, 3]
def baseStart_2131645 : Nat := 118140960795 + 2131645 * 2 ^ 59
def prefixEnd_2131645 : Nat := 4983230072969 + 3 ^ 40 * 2131645 * 2
def baseEnd_2131645 : Nat := 1094558469753417662834249

theorem tailTrace_2131645 : CollatzResearch.WordTrace tailWord_2131645 prefixEnd_2131645 1094558469753417662834249 := by
  unfold tailWord_2131645
  simp only [CollatzResearch.WordTrace]
  refine ⟨77747480362421695827132389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51831653574947797218088259 77747480362421695827132389)
  ·
    refine ⟨14577652567954067967587323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77747480362421695827132389 14577652567954067967587323)
    ·
      refine ⟨21866478851931101951380985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14577652567954067967587323 21866478851931101951380985)
      ·
        refine ⟨16399859138948326463535739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21866478851931101951380985 16399859138948326463535739)
        ·
          refine ⟨24599788708422489695303609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16399859138948326463535739 24599788708422489695303609)
          ·
            refine ⟨18449841531316867271477707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24599788708422489695303609 18449841531316867271477707)
            ·
              refine ⟨27674762296975300907216561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18449841531316867271477707 27674762296975300907216561)
              ·
                refine ⟨20756071722731475680412421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27674762296975300907216561 20756071722731475680412421)
                ·
                  refine ⟨3891763448012151690077329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20756071722731475680412421 3891763448012151690077329)
                  ·
                    refine ⟨2918822586009113767557997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3891763448012151690077329 2918822586009113767557997)
                    ·
                      refine ⟨1094558469753417662834249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2918822586009113767557997 1094558469753417662834249)
                      ·
                        rfl

theorem cell23_2131645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_2131645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2131645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2131645 prefixEnd_2131645 := by exact prefixLift 2131645
  have htrace : WordTrace (prefixWord ++ tailWord_2131645) baseStart_2131645 baseEnd_2131645 := by
    simpa [prefixWord, tailWord_2131645, baseEnd_2131645] using wordTrace_append hprefix tailTrace_2131645
  have hstable : (prefixWord ++ tailWord_2131645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131645).length < 2 ^ (prefixWord ++ tailWord_2131645).sum := by decide
  have hdescent : baseEnd_2131645 < baseStart_2131645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131662 : List Nat := [4, 1, 1, 1, 3, 1, 4, 1, 2, 2, 3]
def baseStart_2131662 : Nat := 118140960795 + 2131662 * 2 ^ 59
def prefixEnd_2131662 : Nat := 4983230072969 + 3 ^ 40 * 2131662 * 2
def baseEnd_2131662 : Nat := 1094567198924544096321671

theorem tailTrace_2131662 : CollatzResearch.WordTrace tailWord_2131662 prefixEnd_2131662 1094567198924544096321671 := by
  unfold tailWord_2131662
  simp only [CollatzResearch.WordTrace]
  refine ⟨9718512550420013466312655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51832066935573405153667493 9718512550420013466312655)
  ·
    refine ⟨14577768825630020199468983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9718512550420013466312655 14577768825630020199468983)
    ·
      refine ⟨21866653238445030299203475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14577768825630020199468983 21866653238445030299203475)
      ·
        refine ⟨32799979857667545448805213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21866653238445030299203475 32799979857667545448805213)
        ·
          refine ⟨12299992446625329543301955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32799979857667545448805213 12299992446625329543301955)
          ·
            refine ⟨18449988669937994314952933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12299992446625329543301955 18449988669937994314952933)
            ·
              refine ⟨3459372875613373934053675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18449988669937994314952933 3459372875613373934053675)
              ·
                refine ⟨5189059313420060901080513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3459372875613373934053675 5189059313420060901080513)
                ·
                  refine ⟨3891794485065045675810385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5189059313420060901080513 3891794485065045675810385)
                  ·
                    refine ⟨2918845863798784256857789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3891794485065045675810385 2918845863798784256857789)
                    ·
                      refine ⟨1094567198924544096321671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2918845863798784256857789 1094567198924544096321671)
                      ·
                        rfl

theorem cell23_2131662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 2, 2, 3].length) (baseStart_2131662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2131662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2131662 prefixEnd_2131662 := by exact prefixLift 2131662
  have htrace : WordTrace (prefixWord ++ tailWord_2131662) baseStart_2131662 baseEnd_2131662 := by
    simpa [prefixWord, tailWord_2131662, baseEnd_2131662] using wordTrace_append hprefix tailTrace_2131662
  have hstable : (prefixWord ++ tailWord_2131662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131662).length < 2 ^ (prefixWord ++ tailWord_2131662).sum := by decide
  have hdescent : baseEnd_2131662 < baseStart_2131662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131715 : List Nat := [1, 1, 1, 3, 2, 2, 4, 1, 3, 1, 4]
def baseStart_2131715 : Nat := 118140960795 + 2131715 * 2 ^ 59
def prefixEnd_2131715 : Nat := 4983230072969 + 3 ^ 40 * 2131715 * 2
def baseEnd_2131715 : Nat := 1094594413399232388958927

theorem tailTrace_2131715 : CollatzResearch.WordTrace tailWord_2131715 prefixEnd_2131715 1094594413399232388958927 := by
  unfold tailWord_2131715
  simp only [CollatzResearch.WordTrace]
  refine ⟨77750033472168097782180599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51833355648112065188120399 77750033472168097782180599)
  ·
    refine ⟨116625050208252146673270899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77750033472168097782180599 116625050208252146673270899)
    ·
      refine ⟨174937575312378220009906349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116625050208252146673270899 174937575312378220009906349)
      ·
        refine ⟨65601590742141832503714881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 174937575312378220009906349 65601590742141832503714881)
        ·
          refine ⟨49201193056606374377786161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65601590742141832503714881 49201193056606374377786161)
          ·
            refine ⟨36900894792454780783339621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49201193056606374377786161 36900894792454780783339621)
            ·
              refine ⟨6918917773585271396876179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36900894792454780783339621 6918917773585271396876179)
              ·
                refine ⟨10378376660377907095314269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6918917773585271396876179 10378376660377907095314269)
                ·
                  refine ⟨3891891247641715160742851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10378376660377907095314269 3891891247641715160742851)
                  ·
                    refine ⟨5837836871462572741114277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3891891247641715160742851 5837836871462572741114277)
                    ·
                      refine ⟨1094594413399232388958927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5837836871462572741114277 1094594413399232388958927)
                      ·
                        rfl

theorem cell23_2131715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 3, 1, 4].length) (baseStart_2131715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2131715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2131715 prefixEnd_2131715 := by exact prefixLift 2131715
  have htrace : WordTrace (prefixWord ++ tailWord_2131715) baseStart_2131715 baseEnd_2131715 := by
    simpa [prefixWord, tailWord_2131715, baseEnd_2131715] using wordTrace_append hprefix tailTrace_2131715
  have hstable : (prefixWord ++ tailWord_2131715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131715).length < 2 ^ (prefixWord ++ tailWord_2131715).sum := by decide
  have hdescent : baseEnd_2131715 < baseStart_2131715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131719 : List Nat := [1, 1, 4, 4, 2, 1, 1, 1, 1, 5, 2]
def baseStart_2131719 : Nat := 118140960795 + 2131719 * 2 ^ 59
def prefixEnd_2131719 : Nat := 4983230072969 + 3 ^ 40 * 2131719 * 2
def baseEnd_2131719 : Nat := 1094596467321850373308909

theorem tailTrace_2131719 : CollatzResearch.WordTrace tailWord_2131719 prefixEnd_2131719 1094596467321850373308909 := by
  unfold tailWord_2131719
  simp only [CollatzResearch.WordTrace]
  refine ⟨77750179364153606465326211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51833452909435737643550807 77750179364153606465326211)
  ·
    refine ⟨116625269046230409697989317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77750179364153606465326211 116625269046230409697989317)
    ·
      refine ⟨21867237946168201818372997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116625269046230409697989317 21867237946168201818372997)
      ·
        refine ⟨4100107114906537840944937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21867237946168201818372997 4100107114906537840944937)
        ·
          refine ⟨3075080336179903380708703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4100107114906537840944937 3075080336179903380708703)
          ·
            refine ⟨4612620504269855071063055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3075080336179903380708703 4612620504269855071063055)
            ·
              refine ⟨6918930756404782606594583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4612620504269855071063055 6918930756404782606594583)
              ·
                refine ⟨10378396134607173909891875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6918930756404782606594583 10378396134607173909891875)
                ·
                  refine ⟨15567594201910760864837813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10378396134607173909891875 15567594201910760864837813)
                  ·
                    refine ⟨1459461956429133831078545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15567594201910760864837813 1459461956429133831078545)
                    ·
                      refine ⟨1094596467321850373308909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1459461956429133831078545 1094596467321850373308909)
                      ·
                        rfl

theorem cell23_2131719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_2131719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2131719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2131719 prefixEnd_2131719 := by exact prefixLift 2131719
  have htrace : WordTrace (prefixWord ++ tailWord_2131719) baseStart_2131719 baseEnd_2131719 := by
    simpa [prefixWord, tailWord_2131719, baseEnd_2131719] using wordTrace_append hprefix tailTrace_2131719
  have hstable : (prefixWord ++ tailWord_2131719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131719).length < 2 ^ (prefixWord ++ tailWord_2131719).sum := by decide
  have hdescent : baseEnd_2131719 < baseStart_2131719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131749 : List Nat := [1, 3, 1, 2, 3, 2, 1, 3, 3, 2, 2]
def baseStart_2131749 : Nat := 118140960795 + 2131749 * 2 ^ 59
def prefixEnd_2131749 : Nat := 4983230072969 + 3 ^ 40 * 2131749 * 2
def baseEnd_2131749 : Nat := 1094611871741485255933771

theorem tailTrace_2131749 : CollatzResearch.WordTrace tailWord_2131749 prefixEnd_2131749 1094611871741485255933771 := by
  unfold tailWord_2131749
  simp only [CollatzResearch.WordTrace]
  refine ⟨77751273554044921588918301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51834182369363281059278867 77751273554044921588918301)
  ·
    refine ⟨29156727582766845595844363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77751273554044921588918301 29156727582766845595844363)
    ·
      refine ⟨43735091374150268393766545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29156727582766845595844363 43735091374150268393766545)
      ·
        refine ⟨32801318530612701295324909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43735091374150268393766545 32801318530612701295324909)
        ·
          refine ⟨12300494448979762985746841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32801318530612701295324909 12300494448979762985746841)
          ·
            refine ⟨9225370836734822239310131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12300494448979762985746841 9225370836734822239310131)
            ·
              refine ⟨13838056255102233358965197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9225370836734822239310131 13838056255102233358965197)
              ·
                refine ⟨5189271095663337509611949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13838056255102233358965197 5189271095663337509611949)
                ·
                  refine ⟨1945976660873751566104481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5189271095663337509611949 1945976660873751566104481)
                  ·
                    refine ⟨1459482495655313674578361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1945976660873751566104481 1459482495655313674578361)
                    ·
                      refine ⟨1094611871741485255933771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1459482495655313674578361 1094611871741485255933771)
                      ·
                        rfl

theorem cell23_2131749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 3, 2, 2].length) (baseStart_2131749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2131749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2131749 prefixEnd_2131749 := by exact prefixLift 2131749
  have htrace : WordTrace (prefixWord ++ tailWord_2131749) baseStart_2131749 baseEnd_2131749 := by
    simpa [prefixWord, tailWord_2131749, baseEnd_2131749] using wordTrace_append hprefix tailTrace_2131749
  have hstable : (prefixWord ++ tailWord_2131749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131749).length < 2 ^ (prefixWord ++ tailWord_2131749).sum := by decide
  have hdescent : baseEnd_2131749 < baseStart_2131749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131752 : List Nat := [2, 1, 5, 1, 1, 3, 1, 2, 1, 1, 5]
def baseStart_2131752 : Nat := 118140960795 + 2131752 * 2 ^ 59
def prefixEnd_2131752 : Nat := 4983230072969 + 3 ^ 40 * 2131752 * 2
def baseEnd_2131752 : Nat := 1094613412183448744196257

theorem tailTrace_2131752 : CollatzResearch.WordTrace tailWord_2131752 prefixEnd_2131752 1094613412183448744196257 := by
  unfold tailWord_2131752
  simp only [CollatzResearch.WordTrace]
  refine ⟨38875691486517026550638755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51834255315356035400851673 38875691486517026550638755)
  ·
    refine ⟨58313537229775539825958133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38875691486517026550638755 58313537229775539825958133)
    ·
      refine ⟨5466894115291456858683575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58313537229775539825958133 5466894115291456858683575)
      ·
        refine ⟨8200341172937185288025363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5466894115291456858683575 8200341172937185288025363)
        ·
          refine ⟨12300511759405777932038045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8200341172937185288025363 12300511759405777932038045)
          ·
            refine ⟨4612691909777166724514267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12300511759405777932038045 4612691909777166724514267)
            ·
              refine ⟨6919037864665750086771401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4612691909777166724514267 6919037864665750086771401)
              ·
                refine ⟨5189278398499312565078551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6919037864665750086771401 5189278398499312565078551)
                ·
                  refine ⟨7783917597748968847617827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5189278398499312565078551 7783917597748968847617827)
                  ·
                    refine ⟨11675876396623453271426741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7783917597748968847617827 11675876396623453271426741)
                    ·
                      refine ⟨1094613412183448744196257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11675876396623453271426741 1094613412183448744196257)
                      ·
                        rfl

theorem cell23_2131752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_2131752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2131752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2131752 prefixEnd_2131752 := by exact prefixLift 2131752
  have htrace : WordTrace (prefixWord ++ tailWord_2131752) baseStart_2131752 baseEnd_2131752 := by
    simpa [prefixWord, tailWord_2131752, baseEnd_2131752] using wordTrace_append hprefix tailTrace_2131752
  have hstable : (prefixWord ++ tailWord_2131752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131752).length < 2 ^ (prefixWord ++ tailWord_2131752).sum := by decide
  have hdescent : baseEnd_2131752 < baseStart_2131752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131762 : List Nat := [3, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4]
def baseStart_2131762 : Nat := 118140960795 + 2131762 * 2 ^ 59
def prefixEnd_2131762 : Nat := 4983230072969 + 3 ^ 40 * 2131762 * 2
def baseEnd_2131762 : Nat := 1094618546989993705071211

theorem tailTrace_2131762 : CollatzResearch.WordTrace tailWord_2131762 prefixEnd_2131762 1094618546989993705071211 := by
  unfold tailWord_2131762
  simp only [CollatzResearch.WordTrace]
  refine ⟨19437936925749456202285385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51834498468665216539427693 19437936925749456202285385)
  ·
    refine ⟨14578452694312092151714039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19437936925749456202285385 14578452694312092151714039)
    ·
      refine ⟨21867679041468138227571059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14578452694312092151714039 21867679041468138227571059)
      ·
        refine ⟨32801518562202207341356589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21867679041468138227571059 32801518562202207341356589)
        ·
          refine ⟨12300569460825827753008721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32801518562202207341356589 12300569460825827753008721)
          ·
            refine ⟨9225427095619370814756541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12300569460825827753008721 9225427095619370814756541)
            ·
              refine ⟨3459535160857264055533703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9225427095619370814756541 3459535160857264055533703)
              ·
                refine ⟨5189302741285896083300555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3459535160857264055533703 5189302741285896083300555)
                ·
                  refine ⟨7783954111928844124950833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5189302741285896083300555 7783954111928844124950833)
                  ·
                    refine ⟨5837965583946633093713125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7783954111928844124950833 5837965583946633093713125)
                    ·
                      refine ⟨1094618546989993705071211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5837965583946633093713125 1094618546989993705071211)
                      ·
                        rfl

theorem cell23_2131762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4].length) (baseStart_2131762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2131762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2131762 prefixEnd_2131762 := by exact prefixLift 2131762
  have htrace : WordTrace (prefixWord ++ tailWord_2131762) baseStart_2131762 baseEnd_2131762 := by
    simpa [prefixWord, tailWord_2131762, baseEnd_2131762] using wordTrace_append hprefix tailTrace_2131762
  have hstable : (prefixWord ++ tailWord_2131762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131762).length < 2 ^ (prefixWord ++ tailWord_2131762).sum := by decide
  have hdescent : baseEnd_2131762 < baseStart_2131762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131766 : List Nat := [5, 1, 2, 2, 1, 2, 2, 2, 1, 1, 4]
def baseStart_2131766 : Nat := 118140960795 + 2131766 * 2 ^ 59
def prefixEnd_2131766 : Nat := 4983230072969 + 3 ^ 40 * 2131766 * 2
def baseEnd_2131766 : Nat := 1094620600912611689421193

theorem tailTrace_2131766 : CollatzResearch.WordTrace tailWord_2131766 prefixEnd_2131766 1094620600912611689421193 := by
  unfold tailWord_2131766
  simp only [CollatzResearch.WordTrace]
  refine ⟨4859493349686458343267947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51834595729988888994858101 4859493349686458343267947)
  ·
    refine ⟨7289240024529687514901921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4859493349686458343267947 7289240024529687514901921)
    ·
      refine ⟨5466930018397265636176441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7289240024529687514901921 5466930018397265636176441)
      ·
        refine ⟨4100197513797949227132331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5466930018397265636176441 4100197513797949227132331)
        ·
          refine ⟨6150296270696923840698497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4100197513797949227132331 6150296270696923840698497)
          ·
            refine ⟨4612722203022692880523873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6150296270696923840698497 4612722203022692880523873)
            ·
              refine ⟨3459541652267019660392905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4612722203022692880523873 3459541652267019660392905)
              ·
                refine ⟨2594656239200264745294679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3459541652267019660392905 2594656239200264745294679)
                ·
                  refine ⟨3891984358800397117942019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2594656239200264745294679 3891984358800397117942019)
                  ·
                    refine ⟨5837976538200595676913029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3891984358800397117942019 5837976538200595676913029)
                    ·
                      refine ⟨1094620600912611689421193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5837976538200595676913029 1094620600912611689421193)
                      ·
                        rfl

theorem cell23_2131766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_2131766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2131766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2131766 prefixEnd_2131766 := by exact prefixLift 2131766
  have htrace : WordTrace (prefixWord ++ tailWord_2131766) baseStart_2131766 baseEnd_2131766 := by
    simpa [prefixWord, tailWord_2131766, baseEnd_2131766] using wordTrace_append hprefix tailTrace_2131766
  have hstable : (prefixWord ++ tailWord_2131766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131766).length < 2 ^ (prefixWord ++ tailWord_2131766).sum := by decide
  have hdescent : baseEnd_2131766 < baseStart_2131766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131792 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 5, 3, 2]
def baseStart_2131792 : Nat := 118140960795 + 2131792 * 2 ^ 59
def prefixEnd_2131792 : Nat := 4983230072969 + 3 ^ 40 * 2131792 * 2
def baseEnd_2131792 : Nat := 1094633951409628587696073

theorem tailTrace_2131792 : CollatzResearch.WordTrace tailWord_2131792 prefixEnd_2131792 1094633951409628587696073 := by
  unfold tailWord_2131792
  simp only [CollatzResearch.WordTrace]
  refine ⟨38876420946444569966366815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51835227928592759955155753 38876420946444569966366815)
  ·
    refine ⟨58314631419666854949550223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38876420946444569966366815 58314631419666854949550223)
    ·
      refine ⟨87471947129500282424325335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58314631419666854949550223 87471947129500282424325335)
      ·
        refine ⟨131207920694250423636488003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87471947129500282424325335 131207920694250423636488003)
        ·
          refine ⟨196811881041375635454732005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131207920694250423636488003 196811881041375635454732005)
          ·
            refine ⟨36902227695257931647762251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 196811881041375635454732005 36902227695257931647762251)
            ·
              refine ⟨55353341542886897471643377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36902227695257931647762251 55353341542886897471643377)
              ·
                refine ⟨41515006157165173103732533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55353341542886897471643377 41515006157165173103732533)
                ·
                  refine ⟨3892031827234234978474925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41515006157165173103732533 3892031827234234978474925)
                  ·
                    refine ⟨1459511935212838116928097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3892031827234234978474925 1459511935212838116928097)
                    ·
                      refine ⟨1094633951409628587696073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1459511935212838116928097 1094633951409628587696073)
                      ·
                        rfl

theorem cell23_2131792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 5, 3, 2].length) (baseStart_2131792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2131792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2131792 prefixEnd_2131792 := by exact prefixLift 2131792
  have htrace : WordTrace (prefixWord ++ tailWord_2131792) baseStart_2131792 baseEnd_2131792 := by
    simpa [prefixWord, tailWord_2131792, baseEnd_2131792] using wordTrace_append hprefix tailTrace_2131792
  have hstable : (prefixWord ++ tailWord_2131792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131792).length < 2 ^ (prefixWord ++ tailWord_2131792).sum := by decide
  have hdescent : baseEnd_2131792 < baseStart_2131792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131815 : List Nat := [1, 1, 5, 1, 2, 1, 2, 1, 1, 8]
def baseStart_2131815 : Nat := 118140960795 + 2131815 * 2 ^ 59
def prefixEnd_2131815 : Nat := 4983230072969 + 3 ^ 40 * 2131815 * 2
def baseEnd_2131815 : Nat := 364881920488227332569489

theorem tailTrace_2131815 : CollatzResearch.WordTrace tailWord_2131815 prefixEnd_2131815 364881920488227332569489 := by
  unfold tailWord_2131815
  simp only [CollatzResearch.WordTrace]
  refine ⟨77753680771805814860820899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51835787181203876573880599 77753680771805814860820899)
  ·
    refine ⟨116630521157708722291231349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77753680771805814860820899 116630521157708722291231349)
    ·
      refine ⟨10934111358535192714802939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 116630521157708722291231349 10934111358535192714802939)
      ·
        refine ⟨16401167037802789072204409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10934111358535192714802939 16401167037802789072204409)
        ·
          refine ⟨12300875278352091804153307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16401167037802789072204409 12300875278352091804153307)
          ·
            refine ⟨18451312917528137706229961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12300875278352091804153307 18451312917528137706229961)
            ·
              refine ⟨13838484688146103279672471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18451312917528137706229961 13838484688146103279672471)
              ·
                refine ⟨20757727032219154919508707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13838484688146103279672471 20757727032219154919508707)
                ·
                  refine ⟨31136590548328732379263061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20757727032219154919508707 31136590548328732379263061)
                  ·
                    refine ⟨364881920488227332569489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 31136590548328732379263061 364881920488227332569489)
                    ·
                      rfl

theorem cell23_2131815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_2131815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2131815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2131815 prefixEnd_2131815 := by exact prefixLift 2131815
  have htrace : WordTrace (prefixWord ++ tailWord_2131815) baseStart_2131815 baseEnd_2131815 := by
    simpa [prefixWord, tailWord_2131815, baseEnd_2131815] using wordTrace_append hprefix tailTrace_2131815
  have hstable : (prefixWord ++ tailWord_2131815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131815).length < 2 ^ (prefixWord ++ tailWord_2131815).sum := by decide
  have hdescent : baseEnd_2131815 < baseStart_2131815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131825 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 4, 1, 5]
def baseStart_2131825 : Nat := 118140960795 + 2131825 * 2 ^ 59
def prefixEnd_2131825 : Nat := 4983230072969 + 3 ^ 40 * 2131825 * 2
def baseEnd_2131825 : Nat := 1094650896271226958583421

theorem tailTrace_2131825 : CollatzResearch.WordTrace tailWord_2131825 prefixEnd_2131825 1094650896271226958583421 := by
  unfold tailWord_2131825
  simp only [CollatzResearch.WordTrace]
  refine ⟨77754045501769586568684929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51836030334513057712456619 77754045501769586568684929)
  ·
    refine ⟨58315534126327189926513697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77754045501769586568684929 58315534126327189926513697)
    ·
      refine ⟨43736650594745392444885273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58315534126327189926513697 43736650594745392444885273)
      ·
        refine ⟨32802487946059044333663955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43736650594745392444885273 32802487946059044333663955)
        ·
          refine ⟨49203731919088566500495933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32802487946059044333663955 49203731919088566500495933)
          ·
            refine ⟨18451399469658212437685975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49203731919088566500495933 18451399469658212437685975)
            ·
              refine ⟨27677099204487318656528963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18451399469658212437685975 27677099204487318656528963)
              ·
                refine ⟨41515648806730977984793445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27677099204487318656528963 41515648806730977984793445)
                ·
                  refine ⟨7784184151262058372148771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41515648806730977984793445 7784184151262058372148771)
                  ·
                    refine ⟨11676276226893087558223157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7784184151262058372148771 11676276226893087558223157)
                    ·
                      refine ⟨1094650896271226958583421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11676276226893087558223157 1094650896271226958583421)
                      ·
                        rfl

theorem cell23_2131825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_2131825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2131825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2131825 prefixEnd_2131825 := by exact prefixLift 2131825
  have htrace : WordTrace (prefixWord ++ tailWord_2131825) baseStart_2131825 baseEnd_2131825 := by
    simpa [prefixWord, tailWord_2131825, baseEnd_2131825] using wordTrace_append hprefix tailTrace_2131825
  have hstable : (prefixWord ++ tailWord_2131825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131825).length < 2 ^ (prefixWord ++ tailWord_2131825).sum := by decide
  have hdescent : baseEnd_2131825 < baseStart_2131825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131835 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 4, 2, 4]
def baseStart_2131835 : Nat := 118140960795 + 2131835 * 2 ^ 59
def prefixEnd_2131835 : Nat := 4983230072969 + 3 ^ 40 * 2131835 * 2
def baseEnd_2131835 : Nat := 1094656031077771919458375

theorem tailTrace_2131835 : CollatzResearch.WordTrace tailWord_2131835 prefixEnd_2131835 1094656031077771919458375 := by
  unfold tailWord_2131835
  simp only [CollatzResearch.WordTrace]
  refine ⟨77754410231733358276548959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51836273487822238851032639 77754410231733358276548959)
  ·
    refine ⟨116631615347600037414823439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77754410231733358276548959 116631615347600037414823439)
    ·
      refine ⟨174947423021400056122235159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116631615347600037414823439 174947423021400056122235159)
      ·
        refine ⟨262421134532100084183352739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174947423021400056122235159 262421134532100084183352739)
        ·
          refine ⟨393631701798150126275029109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262421134532100084183352739 393631701798150126275029109)
          ·
            refine ⟨36902972043576574338283979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 393631701798150126275029109 36902972043576574338283979)
            ·
              refine ⟨55354458065364861507425969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36902972043576574338283979 55354458065364861507425969)
              ·
                refine ⟨41515843549023646130569477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55354458065364861507425969 41515843549023646130569477)
                ·
                  refine ⟨7784220665441933649481777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41515843549023646130569477 7784220665441933649481777)
                  ·
                    refine ⟨5838165499081450237111333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7784220665441933649481777 5838165499081450237111333)
                    ·
                      refine ⟨1094656031077771919458375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5838165499081450237111333 1094656031077771919458375)
                      ·
                        rfl

theorem cell23_2131835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 2, 4].length) (baseStart_2131835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2131835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2131835 prefixEnd_2131835 := by exact prefixLift 2131835
  have htrace : WordTrace (prefixWord ++ tailWord_2131835) baseStart_2131835 baseEnd_2131835 := by
    simpa [prefixWord, tailWord_2131835, baseEnd_2131835] using wordTrace_append hprefix tailTrace_2131835
  have hstable : (prefixWord ++ tailWord_2131835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131835).length < 2 ^ (prefixWord ++ tailWord_2131835).sum := by decide
  have hdescent : baseEnd_2131835 < baseStart_2131835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131875 : List Nat := [1, 1, 1, 4, 1, 2, 1, 4, 1, 7]
def baseStart_2131875 : Nat := 118140960795 + 2131875 * 2 ^ 59
def prefixEnd_2131875 : Nat := 4983230072969 + 3 ^ 40 * 2131875 * 2
def baseEnd_2131875 : Nat := 364892190101317254319397

theorem tailTrace_2131875 : CollatzResearch.WordTrace tailWord_2131875 prefixEnd_2131875 364892190101317254319397 := by
  unfold tailWord_2131875
  simp only [CollatzResearch.WordTrace]
  refine ⟨77755869151588445108005079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51837246101058963405336719 77755869151588445108005079)
  ·
    refine ⟨116633803727382667662007619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77755869151588445108005079 116633803727382667662007619)
    ·
      refine ⟨174950705591074001493011429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116633803727382667662007619 174950705591074001493011429)
      ·
        refine ⟨32803257298326375279939643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 174950705591074001493011429 32803257298326375279939643)
        ·
          refine ⟨49204885947489562919909465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32803257298326375279939643 49204885947489562919909465)
          ·
            refine ⟨36903664460617172189932099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49204885947489562919909465 36903664460617172189932099)
            ·
              refine ⟨55355496690925758284898149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36903664460617172189932099 55355496690925758284898149)
              ·
                refine ⟨10379155629548579678418403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55355496690925758284898149 10379155629548579678418403)
                ·
                  refine ⟨15568733444322869517627605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10379155629548579678418403 15568733444322869517627605)
                  ·
                    refine ⟨364892190101317254319397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15568733444322869517627605 364892190101317254319397)
                    ·
                      rfl

theorem cell23_2131875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 7].length) (baseStart_2131875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2131875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2131875 prefixEnd_2131875 := by exact prefixLift 2131875
  have htrace : WordTrace (prefixWord ++ tailWord_2131875) baseStart_2131875 baseEnd_2131875 := by
    simpa [prefixWord, tailWord_2131875, baseEnd_2131875] using wordTrace_append hprefix tailTrace_2131875
  have hstable : (prefixWord ++ tailWord_2131875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131875).length < 2 ^ (prefixWord ++ tailWord_2131875).sum := by decide
  have hdescent : baseEnd_2131875 < baseStart_2131875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131939 : List Nat := [1, 1, 1, 6, 1, 2, 2, 2, 3, 4]
def baseStart_2131939 : Nat := 118140960795 + 2131939 * 2 ^ 59
def prefixEnd_2131939 : Nat := 4983230072969 + 3 ^ 40 * 2131939 * 2
def baseEnd_2131939 : Nat := 364903144355279837519299

theorem tailTrace_2131939 : CollatzResearch.WordTrace tailWord_2131939 prefixEnd_2131939 364903144355279837519299 := by
  unfold tailWord_2131939
  simp only [CollatzResearch.WordTrace]
  refine ⟨77758203423356584038334871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51838802282237722692223247 77758203423356584038334871)
  ·
    refine ⟨116637305135034876057502307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77758203423356584038334871 116637305135034876057502307)
    ·
      refine ⟨174955957702552314086253461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116637305135034876057502307 174955957702552314086253461)
      ·
        refine ⟨8201060517307139722793131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 174955957702552314086253461 8201060517307139722793131)
        ·
          refine ⟨12301590775960709584189697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8201060517307139722793131 12301590775960709584189697)
          ·
            refine ⟨9226193081970532188142273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12301590775960709584189697 9226193081970532188142273)
            ·
              refine ⟨6919644811477899141106705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9226193081970532188142273 6919644811477899141106705)
              ·
                refine ⟨5189733608608424355830029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6919644811477899141106705 5189733608608424355830029)
                ·
                  refine ⟨1946150103228159133436261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5189733608608424355830029 1946150103228159133436261)
                  ·
                    refine ⟨364903144355279837519299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1946150103228159133436261 364903144355279837519299)
                    ·
                      rfl

theorem cell23_2131939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 3, 4].length) (baseStart_2131939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2131939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2131939 prefixEnd_2131939 := by exact prefixLift 2131939
  have htrace : WordTrace (prefixWord ++ tailWord_2131939) baseStart_2131939 baseEnd_2131939 := by
    simpa [prefixWord, tailWord_2131939, baseEnd_2131939] using wordTrace_append hprefix tailTrace_2131939
  have hstable : (prefixWord ++ tailWord_2131939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131939).length < 2 ^ (prefixWord ++ tailWord_2131939).sum := by decide
  have hdescent : baseEnd_2131939 < baseStart_2131939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131945 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 9]
def baseStart_2131945 : Nat := 118140960795 + 2131945 * 2 ^ 59
def prefixEnd_2131945 : Nat := 4983230072969 + 3 ^ 40 * 2131945 * 2
def baseEnd_2131945 : Nat := 1094712513949766489082869

theorem tailTrace_2131945 : CollatzResearch.WordTrace tailWord_2131945 prefixEnd_2131945 1094712513949766489082869 := by
  unfold tailWord_2131945
  simp only [CollatzResearch.WordTrace]
  refine ⟨77758422261334847063053289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51838948174223231375368859 77758422261334847063053289)
  ·
    refine ⟨58318816696001135297289967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77758422261334847063053289 58318816696001135297289967)
    ·
      refine ⟨87478225044001702945934951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58318816696001135297289967 87478225044001702945934951)
      ·
        refine ⟨131217337566002554418902427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87478225044001702945934951 131217337566002554418902427)
        ·
          refine ⟨196826006349003831628353641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131217337566002554418902427 196826006349003831628353641)
          ·
            refine ⟨147619504761752873721265231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196826006349003831628353641 147619504761752873721265231)
            ·
              refine ⟨221429257142629310581897847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147619504761752873721265231 221429257142629310581897847)
              ·
                refine ⟨332143885713943965872846771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 221429257142629310581897847 332143885713943965872846771)
                ·
                  refine ⟨498215828570915948809270157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 332143885713943965872846771 498215828570915948809270157)
                  ·
                    refine ⟨186830935714093480803476309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 498215828570915948809270157 186830935714093480803476309)
                    ·
                      refine ⟨1094712513949766489082869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 186830935714093480803476309 1094712513949766489082869)
                      ·
                        rfl

theorem cell23_2131945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 9].length) (baseStart_2131945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2131945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2131945 prefixEnd_2131945 := by exact prefixLift 2131945
  have htrace : WordTrace (prefixWord ++ tailWord_2131945) baseStart_2131945 baseEnd_2131945 := by
    simpa [prefixWord, tailWord_2131945, baseEnd_2131945] using wordTrace_append hprefix tailTrace_2131945
  have hstable : (prefixWord ++ tailWord_2131945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131945).length < 2 ^ (prefixWord ++ tailWord_2131945).sum := by decide
  have hdescent : baseEnd_2131945 < baseStart_2131945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131966 : List Nat := [4, 2, 2, 2, 1, 1, 1, 1, 4, 2, 3]
def baseStart_2131966 : Nat := 118140960795 + 2131966 * 2 ^ 59
def prefixEnd_2131966 : Nat := 4983230072969 + 3 ^ 40 * 2131966 * 2
def baseEnd_2131966 : Nat := 1094723297043510906920273

theorem tailTrace_2131966 : CollatzResearch.WordTrace tailWord_2131966 prefixEnd_2131966 1094723297043510906920273 := by
  unfold tailWord_2131966
  simp only [CollatzResearch.WordTrace]
  refine ⟨9719898524282345956195969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51839458796172511766378501 9719898524282345956195969)
  ·
    refine ⟨7289923893211759467146977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9719898524282345956195969 7289923893211759467146977)
    ·
      refine ⟨5467442919908819600360233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7289923893211759467146977 5467442919908819600360233)
      ·
        refine ⟨4100582189931614700270175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5467442919908819600360233 4100582189931614700270175)
        ·
          refine ⟨6150873284897422050405263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4100582189931614700270175 6150873284897422050405263)
          ·
            refine ⟨9226309927346133075607895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6150873284897422050405263 9226309927346133075607895)
            ·
              refine ⟨13839464891019199613411843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9226309927346133075607895 13839464891019199613411843)
              ·
                refine ⟨20759197336528799420117765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13839464891019199613411843 20759197336528799420117765)
                ·
                  refine ⟨3892349500599149891272081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20759197336528799420117765 3892349500599149891272081)
                  ·
                    refine ⟨2919262125449362418454061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3892349500599149891272081 2919262125449362418454061)
                    ·
                      refine ⟨1094723297043510906920273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2919262125449362418454061 1094723297043510906920273)
                      ·
                        rfl

theorem cell23_2131966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_2131966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2131966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2131966 prefixEnd_2131966 := by exact prefixLift 2131966
  have htrace : WordTrace (prefixWord ++ tailWord_2131966) baseStart_2131966 baseEnd_2131966 := by
    simpa [prefixWord, tailWord_2131966, baseEnd_2131966] using wordTrace_append hprefix tailTrace_2131966
  have hstable : (prefixWord ++ tailWord_2131966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131966).length < 2 ^ (prefixWord ++ tailWord_2131966).sum := by decide
  have hdescent : baseEnd_2131966 < baseStart_2131966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131973 : List Nat := [1, 3, 1, 1, 2, 5, 3, 2, 1, 4]
def baseStart_2131973 : Nat := 118140960795 + 2131973 * 2 ^ 59
def prefixEnd_2131973 : Nat := 4983230072969 + 3 ^ 40 * 2131973 * 2
def baseEnd_2131973 : Nat := 364908963802697459844247

theorem tailTrace_2131973 : CollatzResearch.WordTrace tailWord_2131973 prefixEnd_2131973 364908963802697459844247 := by
  unfold tailWord_2131973
  simp only [CollatzResearch.WordTrace]
  refine ⟨77759443505233407845072573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51839629003488938563381715 77759443505233407845072573)
  ·
    refine ⟨29159791314462527941902215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77759443505233407845072573 29159791314462527941902215)
    ·
      refine ⟨43739686971693791912853323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29159791314462527941902215 43739686971693791912853323)
      ·
        refine ⟨65609530457540687869279985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43739686971693791912853323 65609530457540687869279985)
        ·
          refine ⟨49207147843155515901959989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65609530457540687869279985 49207147843155515901959989)
          ·
            refine ⟨4613170110295829615808749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49207147843155515901959989 4613170110295829615808749)
            ·
              refine ⟨1729938791360936105928281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4613170110295829615808749 1729938791360936105928281)
              ·
                refine ⟨1297454093520702079446211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1729938791360936105928281 1297454093520702079446211)
                ·
                  refine ⟨1946181140281053119169317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1297454093520702079446211 1946181140281053119169317)
                  ·
                    refine ⟨364908963802697459844247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1946181140281053119169317 364908963802697459844247)
                    ·
                      rfl

theorem cell23_2131973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 2, 1, 4].length) (baseStart_2131973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2131973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2131973 prefixEnd_2131973 := by exact prefixLift 2131973
  have htrace : WordTrace (prefixWord ++ tailWord_2131973) baseStart_2131973 baseEnd_2131973 := by
    simpa [prefixWord, tailWord_2131973, baseEnd_2131973] using wordTrace_append hprefix tailTrace_2131973
  have hstable : (prefixWord ++ tailWord_2131973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131973).length < 2 ^ (prefixWord ++ tailWord_2131973).sum := by decide
  have hdescent : baseEnd_2131973 < baseStart_2131973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132016 : List Nat := [2, 1, 1, 1, 2, 6, 3, 1, 1, 5]
def baseStart_2132016 : Nat := 118140960795 + 2132016 * 2 ^ 59
def prefixEnd_2132016 : Nat := 4983230072969 + 3 ^ 40 * 2132016 * 2
def baseEnd_2132016 : Nat := 364916323692078570431681

theorem tailTrace_2132016 : CollatzResearch.WordTrace tailWord_2132016 prefixEnd_2132016 364916323692078570431681 := by
  unfold tailWord_2132016
  simp only [CollatzResearch.WordTrace]
  refine ⟨38880505922038813094443951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51840674562718417459258601 38880505922038813094443951)
  ·
    refine ⟨58320758883058219641665927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38880505922038813094443951 58320758883058219641665927)
    ·
      refine ⟨87481138324587329462498891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58320758883058219641665927 87481138324587329462498891)
      ·
        refine ⟨131221707486880994193748337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87481138324587329462498891 131221707486880994193748337)
        ·
          refine ⟨98416280615160745645311253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131221707486880994193748337 98416280615160745645311253)
          ·
            refine ⟨4613263153835659952123965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 98416280615160745645311253 4613263153835659952123965)
            ·
              refine ⟨1729973682688372482046487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4613263153835659952123965 1729973682688372482046487)
              ·
                refine ⟨2594960524032558723069731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1729973682688372482046487 2594960524032558723069731)
                ·
                  refine ⟨3892440786048838084604597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2594960524032558723069731 3892440786048838084604597)
                  ·
                    refine ⟨364916323692078570431681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3892440786048838084604597 364916323692078570431681)
                    ·
                      rfl

theorem cell23_2132016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 1, 1, 5].length) (baseStart_2132016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132016 prefixEnd_2132016 := by exact prefixLift 2132016
  have htrace : WordTrace (prefixWord ++ tailWord_2132016) baseStart_2132016 baseEnd_2132016 := by
    simpa [prefixWord, tailWord_2132016, baseEnd_2132016] using wordTrace_append hprefix tailTrace_2132016
  have hstable : (prefixWord ++ tailWord_2132016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132016).length < 2 ^ (prefixWord ++ tailWord_2132016).sum := by decide
  have hdescent : baseEnd_2132016 < baseStart_2132016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132019 : List Nat := [1, 1, 1, 2, 4, 1, 2, 5, 1, 1, 4]
def baseStart_2132019 : Nat := 118140960795 + 2132019 * 2 ^ 59
def prefixEnd_2132019 : Nat := 4983230072969 + 3 ^ 40 * 2132019 * 2
def baseEnd_2132019 : Nat := 1094750511518199199557529

theorem tailTrace_2132019 : CollatzResearch.WordTrace tailWord_2132019 prefixEnd_2132019 1094750511518199199557529 := by
  unfold tailWord_2132019
  simp only [CollatzResearch.WordTrace]
  refine ⟨77761121263066757701247111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51840747508711171800831407 77761121263066757701247111)
  ·
    refine ⟨116641681894600136551870667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77761121263066757701247111 116641681894600136551870667)
    ·
      refine ⟨174962522841900204827806001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116641681894600136551870667 174962522841900204827806001)
      ·
        refine ⟨131221892131425153620854501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174962522841900204827806001 131221892131425153620854501)
        ·
          refine ⟨24604104774642216303910219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 131221892131425153620854501 24604104774642216303910219)
          ·
            refine ⟨36906157161963324455865329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24604104774642216303910219 36906157161963324455865329)
            ·
              refine ⟨27679617871472493341898997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36906157161963324455865329 27679617871472493341898997)
              ·
                refine ⟨2594964175450546250803031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27679617871472493341898997 2594964175450546250803031)
                ·
                  refine ⟨3892446263175819376204547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2594964175450546250803031 3892446263175819376204547)
                  ·
                    refine ⟨5838669394763729064306821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3892446263175819376204547 5838669394763729064306821)
                    ·
                      refine ⟨1094750511518199199557529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5838669394763729064306821 1094750511518199199557529)
                      ·
                        rfl

theorem cell23_2132019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 5, 1, 1, 4].length) (baseStart_2132019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132019 prefixEnd_2132019 := by exact prefixLift 2132019
  have htrace : WordTrace (prefixWord ++ tailWord_2132019) baseStart_2132019 baseEnd_2132019 := by
    simpa [prefixWord, tailWord_2132019, baseEnd_2132019] using wordTrace_append hprefix tailTrace_2132019
  have hstable : (prefixWord ++ tailWord_2132019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132019).length < 2 ^ (prefixWord ++ tailWord_2132019).sum := by decide
  have hdescent : baseEnd_2132019 < baseStart_2132019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132039 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 5, 2, 3]
def baseStart_2132039 : Nat := 118140960795 + 2132039 * 2 ^ 59
def prefixEnd_2132039 : Nat := 4983230072969 + 3 ^ 40 * 2132039 * 2
def baseEnd_2132039 : Nat := 1094760781131289121307437

theorem tailTrace_2132039 : CollatzResearch.WordTrace tailWord_2132039 prefixEnd_2132039 1094760781131289121307437 := by
  unfold tailWord_2132039
  simp only [CollatzResearch.WordTrace]
  refine ⟨77761850722994301116975171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51841233815329534077983447 77761850722994301116975171)
  ·
    refine ⟨116642776084491451675462757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77761850722994301116975171 116642776084491451675462757)
    ·
      refine ⟨21870520515842147189149267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116642776084491451675462757 21870520515842147189149267)
      ·
        refine ⟨32805780773763220783723901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21870520515842147189149267 32805780773763220783723901)
        ·
          refine ⟨12302167790161207793896463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32805780773763220783723901 12302167790161207793896463)
          ·
            refine ⟨18453251685241811690844695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12302167790161207793896463 18453251685241811690844695)
            ·
              refine ⟨27679877527862717536267043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18453251685241811690844695 27679877527862717536267043)
              ·
                refine ⟨41519816291794076304400565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27679877527862717536267043 41519816291794076304400565)
                ·
                  refine ⟨3892482777355694653537553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41519816291794076304400565 3892482777355694653537553)
                  ·
                    refine ⟨2919362083016770990153165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3892482777355694653537553 2919362083016770990153165)
                    ·
                      refine ⟨1094760781131289121307437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2919362083016770990153165 1094760781131289121307437)
                      ·
                        rfl

theorem cell23_2132039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 5, 2, 3].length) (baseStart_2132039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132039 prefixEnd_2132039 := by exact prefixLift 2132039
  have htrace : WordTrace (prefixWord ++ tailWord_2132039) baseStart_2132039 baseEnd_2132039 := by
    simpa [prefixWord, tailWord_2132039, baseEnd_2132039] using wordTrace_append hprefix tailTrace_2132039
  have hstable : (prefixWord ++ tailWord_2132039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132039).length < 2 ^ (prefixWord ++ tailWord_2132039).sum := by decide
  have hdescent : baseEnd_2132039 < baseStart_2132039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132046 : List Nat := [4, 1, 1, 1, 1, 4, 2, 3, 2, 4]
def baseStart_2132046 : Nat := 118140960795 + 2132046 * 2 ^ 59
def prefixEnd_2132046 : Nat := 4983230072969 + 3 ^ 40 * 2132046 * 2
def baseEnd_2132046 : Nat := 364921458498623531306635

theorem tailTrace_2132046 : CollatzResearch.WordTrace tailWord_2132046 prefixEnd_2132046 364921458498623531306635 := by
  unfold tailWord_2132046
  simp only [CollatzResearch.WordTrace]
  refine ⟨9720263254246117664059999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51841404022645960874986661 9720263254246117664059999)
  ·
    refine ⟨14580394881369176496089999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9720263254246117664059999 14580394881369176496089999)
    ·
      refine ⟨21870592322053764744134999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14580394881369176496089999 21870592322053764744134999)
      ·
        refine ⟨32805888483080647116202499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21870592322053764744134999 32805888483080647116202499)
        ·
          refine ⟨49208832724620970674303749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32805888483080647116202499 49208832724620970674303749)
          ·
            refine ⟨9226656135866432001431953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49208832724620970674303749 9226656135866432001431953)
            ·
              refine ⟨6919992101899824001073965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9226656135866432001431953 6919992101899824001073965)
              ·
                refine ⟨2594997038212434000402737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6919992101899824001073965 2594997038212434000402737)
                ·
                  refine ⟨1946247778659325500302053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2594997038212434000402737 1946247778659325500302053)
                  ·
                    refine ⟨364921458498623531306635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1946247778659325500302053 364921458498623531306635)
                    ·
                      rfl

theorem cell23_2132046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 3, 2, 4].length) (baseStart_2132046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132046 prefixEnd_2132046 := by exact prefixLift 2132046
  have htrace : WordTrace (prefixWord ++ tailWord_2132046) baseStart_2132046 baseEnd_2132046 := by
    simpa [prefixWord, tailWord_2132046, baseEnd_2132046] using wordTrace_append hprefix tailTrace_2132046
  have hstable : (prefixWord ++ tailWord_2132046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132046).length < 2 ^ (prefixWord ++ tailWord_2132046).sum := by decide
  have hdescent : baseEnd_2132046 < baseStart_2132046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132053 : List Nat := [1, 3, 2, 2, 1, 4, 1, 2, 3, 2, 2]
def baseStart_2132053 : Nat := 118140960795 + 2132053 * 2 ^ 59
def prefixEnd_2132053 : Nat := 4983230072969 + 3 ^ 40 * 2132053 * 2
def baseEnd_2132053 : Nat := 1094767969860452066532373

theorem tailTrace_2132053 : CollatzResearch.WordTrace tailWord_2132053 prefixEnd_2132053 1094767969860452066532373 := by
  unfold tailWord_2132053
  simp only [CollatzResearch.WordTrace]
  refine ⟨77762361344943581507984813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51841574229962387671989875 77762361344943581507984813)
  ·
    refine ⟨29160885504353843065494305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77762361344943581507984813 29160885504353843065494305)
    ·
      refine ⟨21870664128265382299120729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29160885504353843065494305 21870664128265382299120729)
      ·
        refine ⟨16402998096199036724340547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21870664128265382299120729 16402998096199036724340547)
        ·
          refine ⟨24604497144298555086510821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16402998096199036724340547 24604497144298555086510821)
          ·
            refine ⟨4613343214555979078720779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24604497144298555086510821 4613343214555979078720779)
            ·
              refine ⟨6920014821833968618081169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4613343214555979078720779 6920014821833968618081169)
              ·
                refine ⟨5190011116375476463560877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6920014821833968618081169 5190011116375476463560877)
                ·
                  refine ⟨1946254168640803673835329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5190011116375476463560877 1946254168640803673835329)
                  ·
                    refine ⟨1459690626480602755376497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1946254168640803673835329 1459690626480602755376497)
                    ·
                      refine ⟨1094767969860452066532373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1459690626480602755376497 1094767969860452066532373)
                      ·
                        rfl

theorem cell23_2132053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 3, 2, 2].length) (baseStart_2132053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132053 prefixEnd_2132053 := by exact prefixLift 2132053
  have htrace : WordTrace (prefixWord ++ tailWord_2132053) baseStart_2132053 baseEnd_2132053 := by
    simpa [prefixWord, tailWord_2132053, baseEnd_2132053] using wordTrace_append hprefix tailTrace_2132053
  have hstable : (prefixWord ++ tailWord_2132053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132053).length < 2 ^ (prefixWord ++ tailWord_2132053).sum := by decide
  have hdescent : baseEnd_2132053 < baseStart_2132053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132129 : List Nat := [1, 2, 3, 3, 1, 2, 1, 1, 1, 3, 5]
def baseStart_2132129 : Nat := 118140960795 + 2132129 * 2 ^ 59
def prefixEnd_2132129 : Nat := 4983230072969 + 3 ^ 40 * 2132129 * 2
def baseEnd_2132129 : Nat := 1094806994390193769182023

theorem tailTrace_2132129 : CollatzResearch.WordTrace tailWord_2132129 prefixEnd_2132129 1094806994390193769182023 := by
  unfold tailWord_2132129
  simp only [CollatzResearch.WordTrace]
  refine ⟨77765133292668246487751441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51843422195112164325167627 77765133292668246487751441)
  ·
    refine ⟨58323849969501184865813581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77765133292668246487751441 58323849969501184865813581)
    ·
      refine ⟨21871443738562944324680093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58323849969501184865813581 21871443738562944324680093)
      ·
        refine ⟨8201791401961104121755035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21871443738562944324680093 8201791401961104121755035)
        ·
          refine ⟨12302687102941656182632553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8201791401961104121755035 12302687102941656182632553)
          ·
            refine ⟨9227015327206242136974415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12302687102941656182632553 9227015327206242136974415)
            ·
              refine ⟨13840522990809363205461623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9227015327206242136974415 13840522990809363205461623)
              ·
                refine ⟨20760784486214044808192435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13840522990809363205461623 20760784486214044808192435)
                ·
                  refine ⟨31141176729321067212288653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20760784486214044808192435 31141176729321067212288653)
                  ·
                    refine ⟨11677941273495400204608245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31141176729321067212288653 11677941273495400204608245)
                    ·
                      refine ⟨1094806994390193769182023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11677941273495400204608245 1094806994390193769182023)
                      ·
                        rfl

theorem cell23_2132129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_2132129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132129 prefixEnd_2132129 := by exact prefixLift 2132129
  have htrace : WordTrace (prefixWord ++ tailWord_2132129) baseStart_2132129 baseEnd_2132129 := by
    simpa [prefixWord, tailWord_2132129, baseEnd_2132129] using wordTrace_append hprefix tailTrace_2132129
  have hstable : (prefixWord ++ tailWord_2132129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132129).length < 2 ^ (prefixWord ++ tailWord_2132129).sum := by decide
  have hdescent : baseEnd_2132129 < baseStart_2132129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132130 : List Nat := [3, 3, 1, 3, 1, 1, 2, 3, 1, 3, 2]
def baseStart_2132130 : Nat := 118140960795 + 2132130 * 2 ^ 59
def prefixEnd_2132130 : Nat := 4983230072969 + 3 ^ 40 * 2132130 * 2
def baseEnd_2132130 : Nat := 1094807507870848265269519

theorem tailTrace_2132130 : CollatzResearch.WordTrace tailWord_2132130 prefixEnd_2132130 1094807507870848265269519 := by
  unfold tailWord_2132130
  simp only [CollatzResearch.WordTrace]
  refine ⟨19441292441416155914634461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51843446510443082439025229 19441292441416155914634461)
  ·
    refine ⟨7290484665531058467987923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19441292441416155914634461 7290484665531058467987923)
    ·
      refine ⟨10935726998296587701981885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7290484665531058467987923 10935726998296587701981885)
      ·
        refine ⟨4100897624361220388243207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10935726998296587701981885 4100897624361220388243207)
        ·
          refine ⟨6151346436541830582364811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4100897624361220388243207 6151346436541830582364811)
          ·
            refine ⟨9227019654812745873547217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6151346436541830582364811 9227019654812745873547217)
            ·
              refine ⟨6920264741109559405160413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9227019654812745873547217 6920264741109559405160413)
              ·
                refine ⟨2595099277916084776935155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6920264741109559405160413 2595099277916084776935155)
                ·
                  refine ⟨3892648916874127165402733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2595099277916084776935155 3892648916874127165402733)
                  ·
                    refine ⟨1459743343827797687026025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3892648916874127165402733 1459743343827797687026025)
                    ·
                      refine ⟨1094807507870848265269519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1459743343827797687026025 1094807507870848265269519)
                      ·
                        rfl

theorem cell23_2132130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_2132130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132130 prefixEnd_2132130 := by exact prefixLift 2132130
  have htrace : WordTrace (prefixWord ++ tailWord_2132130) baseStart_2132130 baseEnd_2132130 := by
    simpa [prefixWord, tailWord_2132130, baseEnd_2132130] using wordTrace_append hprefix tailTrace_2132130
  have hstable : (prefixWord ++ tailWord_2132130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132130).length < 2 ^ (prefixWord ++ tailWord_2132130).sum := by decide
  have hdescent : baseEnd_2132130 < baseStart_2132130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132143 : List Nat := [1, 1, 2, 1, 2, 3, 1, 6, 2, 2, 2]
def baseStart_2132143 : Nat := 118140960795 + 2132143 * 2 ^ 59
def prefixEnd_2132143 : Nat := 4983230072969 + 3 ^ 40 * 2132143 * 2
def baseEnd_2132143 : Nat := 1094814183119356714406959

theorem tailTrace_2132143 : CollatzResearch.WordTrace tailWord_2132143 prefixEnd_2132143 1094814183119356714406959 := by
  unfold tailWord_2132143
  simp only [CollatzResearch.WordTrace]
  refine ⟨77765643914617526878761083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51843762609745017919174055 77765643914617526878761083)
  ·
    refine ⟨116648465871926290318141625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77765643914617526878761083 116648465871926290318141625)
    ·
      refine ⟨87486349403944717738606219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116648465871926290318141625 87486349403944717738606219)
      ·
        refine ⟨131229524105917076607909329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87486349403944717738606219 131229524105917076607909329)
        ·
          refine ⟨98422143079437807455931997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131229524105917076607909329 98422143079437807455931997)
          ·
            refine ⟨36908303654789177795974499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98422143079437807455931997 36908303654789177795974499)
            ·
              refine ⟨55362455482183766693961749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36908303654789177795974499 55362455482183766693961749)
              ·
                refine ⟨2595115100727364063779457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 55362455482183766693961749 2595115100727364063779457)
                ·
                  refine ⟨1946336325545523047834593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2595115100727364063779457 1946336325545523047834593)
                  ·
                    refine ⟨1459752244159142285875945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1946336325545523047834593 1459752244159142285875945)
                    ·
                      refine ⟨1094814183119356714406959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1459752244159142285875945 1094814183119356714406959)
                      ·
                        rfl

theorem cell23_2132143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 6, 2, 2, 2].length) (baseStart_2132143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132143 prefixEnd_2132143 := by exact prefixLift 2132143
  have htrace : WordTrace (prefixWord ++ tailWord_2132143) baseStart_2132143 baseEnd_2132143 := by
    simpa [prefixWord, tailWord_2132143, baseEnd_2132143] using wordTrace_append hprefix tailTrace_2132143
  have hstable : (prefixWord ++ tailWord_2132143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132143).length < 2 ^ (prefixWord ++ tailWord_2132143).sum := by decide
  have hdescent : baseEnd_2132143 < baseStart_2132143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132159 : List Nat := [1, 1, 2, 2, 2, 2, 1, 3, 1, 5, 3]
def baseStart_2132159 : Nat := 118140960795 + 2132159 * 2 ^ 59
def prefixEnd_2132159 : Nat := 4983230072969 + 3 ^ 40 * 2132159 * 2
def baseEnd_2132159 : Nat := 1094822398809828651806885

theorem tailTrace_2132159 : CollatzResearch.WordTrace tailWord_2132159 prefixEnd_2132159 1094822398809828651806885 := by
  unfold tailWord_2132159
  simp only [CollatzResearch.WordTrace]
  refine ⟨77766227482559561611343531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51844151655039707740895687 77766227482559561611343531)
  ·
    refine ⟨116649341223839342417015297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77766227482559561611343531 116649341223839342417015297)
    ·
      refine ⟨87487005917879506812761473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116649341223839342417015297 87487005917879506812761473)
      ·
        refine ⟨65615254438409630109571105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87487005917879506812761473 65615254438409630109571105)
        ·
          refine ⟨49211440828807222582178329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65615254438409630109571105 49211440828807222582178329)
          ·
            refine ⟨36908580621605416936633747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49211440828807222582178329 36908580621605416936633747)
            ·
              refine ⟨55362870932408125404950621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36908580621605416936633747 55362870932408125404950621)
              ·
                refine ⟨20761076599653047026856483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55362870932408125404950621 20761076599653047026856483)
                ·
                  refine ⟨31141614899479570540284725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20761076599653047026856483 31141614899479570540284725)
                  ·
                    refine ⟨2919526396826209738151693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31141614899479570540284725 2919526396826209738151693)
                    ·
                      refine ⟨1094822398809828651806885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2919526396826209738151693 1094822398809828651806885)
                      ·
                        rfl

theorem cell23_2132159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 5, 3].length) (baseStart_2132159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132159 prefixEnd_2132159 := by exact prefixLift 2132159
  have htrace : WordTrace (prefixWord ++ tailWord_2132159) baseStart_2132159 baseEnd_2132159 := by
    simpa [prefixWord, tailWord_2132159, baseEnd_2132159] using wordTrace_append hprefix tailTrace_2132159
  have hstable : (prefixWord ++ tailWord_2132159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132159).length < 2 ^ (prefixWord ++ tailWord_2132159).sum := by decide
  have hdescent : baseEnd_2132159 < baseStart_2132159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132160 : List Nat := [2, 1, 1, 2, 5, 2, 1, 3, 2, 2, 2]
def baseStart_2132160 : Nat := 118140960795 + 2132160 * 2 ^ 59
def prefixEnd_2132160 : Nat := 4983230072969 + 3 ^ 40 * 2132160 * 2
def baseEnd_2132160 : Nat := 1094822912290483147894381

theorem tailTrace_2132160 : CollatzResearch.WordTrace tailWord_2132160 prefixEnd_2132160 1094822912290483147894381 := by
  unfold tailWord_2132160
  simp only [CollatzResearch.WordTrace]
  refine ⟨38883131977777969391064967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51844175970370625854753289 38883131977777969391064967)
  ·
    refine ⟨58324697966666954086597451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38883131977777969391064967 58324697966666954086597451)
    ·
      refine ⟨87487046950000431129896177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58324697966666954086597451 87487046950000431129896177)
      ·
        refine ⟨65615285212500323347422133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87487046950000431129896177 65615285212500323347422133)
        ·
          refine ⟨6151432988671905313820825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65615285212500323347422133 6151432988671905313820825)
          ·
            refine ⟨4613574741503928985365619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6151432988671905313820825 4613574741503928985365619)
            ·
              refine ⟨6920362112255893478048429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4613574741503928985365619 6920362112255893478048429)
              ·
                refine ⟨2595135792095960054268161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6920362112255893478048429 2595135792095960054268161)
                ·
                  refine ⟨1946351844071970040701121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2595135792095960054268161 1946351844071970040701121)
                  ·
                    refine ⟨1459763883053977530525841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1946351844071970040701121 1459763883053977530525841)
                    ·
                      refine ⟨1094822912290483147894381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1459763883053977530525841 1094822912290483147894381)
                      ·
                        rfl

theorem cell23_2132160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 3, 2, 2, 2].length) (baseStart_2132160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132160 prefixEnd_2132160 := by exact prefixLift 2132160
  have htrace : WordTrace (prefixWord ++ tailWord_2132160) baseStart_2132160 baseEnd_2132160 := by
    simpa [prefixWord, tailWord_2132160, baseEnd_2132160] using wordTrace_append hprefix tailTrace_2132160
  have hstable : (prefixWord ++ tailWord_2132160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132160).length < 2 ^ (prefixWord ++ tailWord_2132160).sum := by decide
  have hdescent : baseEnd_2132160 < baseStart_2132160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132200 : List Nat := [2, 1, 4, 1, 2, 4, 2, 2, 5]
def baseStart_2132200 : Nat := 118140960795 + 2132200 * 2 ^ 59
def prefixEnd_2132200 : Nat := 4983230072969 + 3 ^ 40 * 2132200 * 2
def baseEnd_2132200 : Nat := 121649272390740332377133

theorem tailTrace_2132200 : CollatzResearch.WordTrace tailWord_2132200 prefixEnd_2132200 121649272390740332377133 := by
  unfold tailWord_2132200
  simp only [CollatzResearch.WordTrace]
  refine ⟨38883861437705512806793027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51845148583607350409057369 38883861437705512806793027)
  ·
    refine ⟨58325792156558269210189541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38883861437705512806793027 58325792156558269210189541)
    ·
      refine ⟨10936086029354675476910539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58325792156558269210189541 10936086029354675476910539)
      ·
        refine ⟨16404129044032013215365809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10936086029354675476910539 16404129044032013215365809)
        ·
          refine ⟨12303096783024009911524357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16404129044032013215365809 12303096783024009911524357)
          ·
            refine ⟨2306830646817001858410817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12303096783024009911524357 2306830646817001858410817)
            ·
              refine ⟨1730122985112751393808113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2306830646817001858410817 1730122985112751393808113)
              ·
                refine ⟨1297592238834563545356085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1730122985112751393808113 1297592238834563545356085)
                ·
                  refine ⟨121649272390740332377133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1297592238834563545356085 121649272390740332377133)
                  ·
                    rfl

theorem cell23_2132200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 2, 5].length) (baseStart_2132200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132200 prefixEnd_2132200 := by exact prefixLift 2132200
  have htrace : WordTrace (prefixWord ++ tailWord_2132200) baseStart_2132200 baseEnd_2132200 := by
    simpa [prefixWord, tailWord_2132200, baseEnd_2132200] using wordTrace_append hprefix tailTrace_2132200
  have hstable : (prefixWord ++ tailWord_2132200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132200).length < 2 ^ (prefixWord ++ tailWord_2132200).sum := by decide
  have hdescent : baseEnd_2132200 < baseStart_2132200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132229 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 1, 6, 4]
def baseStart_2132229 : Nat := 118140960795 + 2132229 * 2 ^ 59
def prefixEnd_2132229 : Nat := 4983230072969 + 3 ^ 40 * 2132229 * 2
def baseEnd_2132229 : Nat := 1094858342455643377931563

theorem tailTrace_2132229 : CollatzResearch.WordTrace tailWord_2132229 prefixEnd_2132229 1094858342455643377931563 := by
  unfold tailWord_2132229
  simp only [CollatzResearch.WordTrace]
  refine ⟨77768780592305963566391741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51845853728203975710927827 77768780592305963566391741)
  ·
    refine ⟨29163292722114736337396903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77768780592305963566391741 29163292722114736337396903)
    ·
      refine ⟨43744939083172104506095355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29163292722114736337396903 43744939083172104506095355)
      ·
        refine ⟨65617408624758156759143033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43744939083172104506095355 65617408624758156759143033)
        ·
          refine ⟨49213056468568617569357275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65617408624758156759143033 49213056468568617569357275)
          ·
            refine ⟨73819584702852926354035913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49213056468568617569357275 73819584702852926354035913)
            ·
              refine ⟨55364688527139694765526935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73819584702852926354035913 55364688527139694765526935)
              ·
                refine ⟨83047032790709542148290403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55364688527139694765526935 83047032790709542148290403)
                ·
                  refine ⟨124570549186064313222435605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83047032790709542148290403 124570549186064313222435605)
                  ·
                    refine ⟨5839244493096764682301669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 124570549186064313222435605 5839244493096764682301669)
                    ·
                      refine ⟨1094858342455643377931563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5839244493096764682301669 1094858342455643377931563)
                      ·
                        rfl

theorem cell23_2132229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 6, 4].length) (baseStart_2132229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132229 prefixEnd_2132229 := by exact prefixLift 2132229
  have htrace : WordTrace (prefixWord ++ tailWord_2132229) baseStart_2132229 baseEnd_2132229 := by
    simpa [prefixWord, tailWord_2132229, baseEnd_2132229] using wordTrace_append hprefix tailTrace_2132229
  have hstable : (prefixWord ++ tailWord_2132229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132229).length < 2 ^ (prefixWord ++ tailWord_2132229).sum := by decide
  have hdescent : baseEnd_2132229 < baseStart_2132229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132233 : List Nat := [1, 2, 1, 1, 3, 6, 1, 1, 2, 1, 4]
def baseStart_2132233 : Nat := 118140960795 + 2132233 * 2 ^ 59
def prefixEnd_2132233 : Nat := 4983230072969 + 3 ^ 40 * 2132233 * 2
def baseEnd_2132233 : Nat := 1094860396378261362281545

theorem tailTrace_2132233 : CollatzResearch.WordTrace tailWord_2132233 prefixEnd_2132233 1094860396378261362281545 := by
  unfold tailWord_2132233
  simp only [CollatzResearch.WordTrace]
  refine ⟨77768926484291472249537353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51845950989527648166358235 77768926484291472249537353)
  ·
    refine ⟨58326694863218604187153015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77768926484291472249537353 58326694863218604187153015)
    ·
      refine ⟨87490042294827906280729523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58326694863218604187153015 87490042294827906280729523)
      ·
        refine ⟨131235063442241859421094285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87490042294827906280729523 131235063442241859421094285)
        ·
          refine ⟨49213148790840697282910357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131235063442241859421094285 49213148790840697282910357)
          ·
            refine ⟨2306866349570657685136423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 49213148790840697282910357 2306866349570657685136423)
            ·
              refine ⟨3460299524355986527704635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2306866349570657685136423 3460299524355986527704635)
              ·
                refine ⟨5190449286533979791556953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3460299524355986527704635 5190449286533979791556953)
                ·
                  refine ⟨3892836964900484843667715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5190449286533979791556953 3892836964900484843667715)
                  ·
                    refine ⟨5839255447350727265501573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3892836964900484843667715 5839255447350727265501573)
                    ·
                      refine ⟨1094860396378261362281545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5839255447350727265501573 1094860396378261362281545)
                      ·
                        rfl

theorem cell23_2132233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 2, 1, 4].length) (baseStart_2132233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132233 prefixEnd_2132233 := by exact prefixLift 2132233
  have htrace : WordTrace (prefixWord ++ tailWord_2132233) baseStart_2132233 baseEnd_2132233 := by
    simpa [prefixWord, tailWord_2132233, baseEnd_2132233] using wordTrace_append hprefix tailTrace_2132233
  have hstable : (prefixWord ++ tailWord_2132233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132233).length < 2 ^ (prefixWord ++ tailWord_2132233).sum := by decide
  have hdescent : baseEnd_2132233 < baseStart_2132233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132236 : List Nat := [2, 2, 1, 2, 2, 2, 3, 1, 1, 4, 3]
def baseStart_2132236 : Nat := 118140960795 + 2132236 * 2 ^ 59
def prefixEnd_2132236 : Nat := 4983230072969 + 3 ^ 40 * 2132236 * 2
def baseEnd_2132236 : Nat := 1094861936820224850544031

theorem tailTrace_2132236 : CollatzResearch.WordTrace tailWord_2132236 prefixEnd_2132236 1094861936820224850544031 := by
  unfold tailWord_2132236
  simp only [CollatzResearch.WordTrace]
  refine ⟨38884517951640301880948281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51846023935520402507931041 38884517951640301880948281)
  ·
    refine ⟨29163388463730226410711211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38884517951640301880948281 29163388463730226410711211)
    ·
      refine ⟨43745082695595339616066817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29163388463730226410711211 43745082695595339616066817)
      ·
        refine ⟨32808812021696504712050113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43745082695595339616066817 32808812021696504712050113)
        ·
          refine ⟨24606609016272378534037585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32808812021696504712050113 24606609016272378534037585)
          ·
            refine ⟨18454956762204283900528189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24606609016272378534037585 18454956762204283900528189)
            ·
              refine ⟨6920608785826606462698071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18454956762204283900528189 6920608785826606462698071)
              ·
                refine ⟨10380913178739909694047107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6920608785826606462698071 10380913178739909694047107)
                ·
                  refine ⟨15571369768109864541070661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10380913178739909694047107 15571369768109864541070661)
                  ·
                    refine ⟨2919631831520599601450749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15571369768109864541070661 2919631831520599601450749)
                    ·
                      refine ⟨1094861936820224850544031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2919631831520599601450749 1094861936820224850544031)
                      ·
                        rfl

theorem cell23_2132236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 1, 4, 3].length) (baseStart_2132236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132236 prefixEnd_2132236 := by exact prefixLift 2132236
  have htrace : WordTrace (prefixWord ++ tailWord_2132236) baseStart_2132236 baseEnd_2132236 := by
    simpa [prefixWord, tailWord_2132236, baseEnd_2132236] using wordTrace_append hprefix tailTrace_2132236
  have hstable : (prefixWord ++ tailWord_2132236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132236).length < 2 ^ (prefixWord ++ tailWord_2132236).sum := by decide
  have hdescent : baseEnd_2132236 < baseStart_2132236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132256 : List Nat := [2, 1, 1, 5, 2, 2, 1, 1, 8]
def baseStart_2132256 : Nat := 118140960795 + 2132256 * 2 ^ 59
def prefixEnd_2132256 : Nat := 4983230072969 + 3 ^ 40 * 2132256 * 2
def baseEnd_2132256 : Nat := 121652467381479419143771

theorem tailTrace_2132256 : CollatzResearch.WordTrace tailWord_2132256 prefixEnd_2132256 121652467381479419143771 := by
  unfold tailWord_2132256
  simp only [CollatzResearch.WordTrace]
  refine ⟨38884882681604073588812311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51846510242138764785083081 38884882681604073588812311)
  ·
    refine ⟨58327324022406110383218467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38884882681604073588812311 58327324022406110383218467)
    ·
      refine ⟨87490986033609165574827701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58327324022406110383218467 87490986033609165574827701)
      ·
        refine ⟨8202279940650859272640097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 87490986033609165574827701 8202279940650859272640097)
        ·
          refine ⟨6151709955488144454480073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8202279940650859272640097 6151709955488144454480073)
          ·
            refine ⟨4613782466616108340860055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6151709955488144454480073 4613782466616108340860055)
            ·
              refine ⟨6920673699924162511290083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4613782466616108340860055 6920673699924162511290083)
              ·
                refine ⟨10381010549886243766935125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6920673699924162511290083 10381010549886243766935125)
                ·
                  refine ⟨121652467381479419143771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10381010549886243766935125 121652467381479419143771)
                  ·
                    rfl

theorem cell23_2132256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 8].length) (baseStart_2132256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132256 prefixEnd_2132256 := by exact prefixLift 2132256
  have htrace : WordTrace (prefixWord ++ tailWord_2132256) baseStart_2132256 baseEnd_2132256 := by
    simpa [prefixWord, tailWord_2132256, baseEnd_2132256] using wordTrace_append hprefix tailTrace_2132256
  have hstable : (prefixWord ++ tailWord_2132256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132256).length < 2 ^ (prefixWord ++ tailWord_2132256).sum := by decide
  have hdescent : baseEnd_2132256 < baseStart_2132256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132259 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 8]
def baseStart_2132259 : Nat := 118140960795 + 2132259 * 2 ^ 59
def prefixEnd_2132259 : Nat := 4983230072969 + 3 ^ 40 * 2132259 * 2
def baseEnd_2132259 : Nat := 1094873746875278260556425

theorem tailTrace_2132259 : CollatzResearch.WordTrace tailWord_2132259 prefixEnd_2132259 1094873746875278260556425 := by
  unfold tailWord_2132259
  simp only [CollatzResearch.WordTrace]
  refine ⟨77769874782197278689983831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51846583188131519126655887 77769874782197278689983831)
  ·
    refine ⟨116654812173295918034975747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77769874782197278689983831 116654812173295918034975747)
    ·
      refine ⟨174982218259943877052463621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116654812173295918034975747 174982218259943877052463621)
      ·
        refine ⟨32809165923739476947336929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 174982218259943877052463621 32809165923739476947336929)
        ·
          refine ⟨24606874442804607710502697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32809165923739476947336929 24606874442804607710502697)
          ·
            refine ⟨18455155832103455782877023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24606874442804607710502697 18455155832103455782877023)
            ·
              refine ⟨27682733748155183674315535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18455155832103455782877023 27682733748155183674315535)
              ·
                refine ⟨41524100622232775511473303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27682733748155183674315535 41524100622232775511473303)
                ·
                  refine ⟨62286150933349163267209955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41524100622232775511473303 62286150933349163267209955)
                  ·
                    refine ⟨93429226400023744900814933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 62286150933349163267209955 93429226400023744900814933)
                    ·
                      refine ⟨1094873746875278260556425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 93429226400023744900814933 1094873746875278260556425)
                      ·
                        rfl

theorem cell23_2132259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_2132259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132259 prefixEnd_2132259 := by exact prefixLift 2132259
  have htrace : WordTrace (prefixWord ++ tailWord_2132259) baseStart_2132259 baseEnd_2132259 := by
    simpa [prefixWord, tailWord_2132259, baseEnd_2132259] using wordTrace_append hprefix tailTrace_2132259
  have hstable : (prefixWord ++ tailWord_2132259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132259).length < 2 ^ (prefixWord ++ tailWord_2132259).sum := by decide
  have hdescent : baseEnd_2132259 < baseStart_2132259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132260 : List Nat := [2, 3, 1, 3, 1, 2, 2, 4, 1, 4]
def baseStart_2132260 : Nat := 118140960795 + 2132260 * 2 ^ 59
def prefixEnd_2132260 : Nat := 4983230072969 + 3 ^ 40 * 2132260 * 2
def baseEnd_2132260 : Nat := 364958086785310918881307

theorem tailTrace_2132260 : CollatzResearch.WordTrace tailWord_2132260 prefixEnd_2132260 364958086785310918881307 := by
  unfold tailWord_2132260
  simp only [CollatzResearch.WordTrace]
  refine ⟨38884955627596827930385117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51846607503462437240513489 38884955627596827930385117)
  ·
    refine ⟨14581858360348810473894419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38884955627596827930385117 14581858360348810473894419)
    ·
      refine ⟨21872787540523215710841629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14581858360348810473894419 21872787540523215710841629)
      ·
        refine ⟨8202295327696205891565611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21872787540523215710841629 8202295327696205891565611)
        ·
          refine ⟨12303442991544308837348417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8202295327696205891565611 12303442991544308837348417)
          ·
            refine ⟨9227582243658231628011313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12303442991544308837348417 9227582243658231628011313)
            ·
              refine ⟨6920686682743673721008485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9227582243658231628011313 6920686682743673721008485)
              ·
                refine ⟨1297628753014438822689091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6920686682743673721008485 1297628753014438822689091)
                ·
                  refine ⟨1946443129521658234033637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1297628753014438822689091 1946443129521658234033637)
                  ·
                    refine ⟨364958086785310918881307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1946443129521658234033637 364958086785310918881307)
                    ·
                      rfl

theorem cell23_2132260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 4, 1, 4].length) (baseStart_2132260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132260 prefixEnd_2132260 := by exact prefixLift 2132260
  have htrace : WordTrace (prefixWord ++ tailWord_2132260) baseStart_2132260 baseEnd_2132260 := by
    simpa [prefixWord, tailWord_2132260, baseEnd_2132260] using wordTrace_append hprefix tailTrace_2132260
  have hstable : (prefixWord ++ tailWord_2132260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132260).length < 2 ^ (prefixWord ++ tailWord_2132260).sum := by decide
  have hdescent : baseEnd_2132260 < baseStart_2132260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132279 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 7]
def baseStart_2132279 : Nat := 118140960795 + 2132279 * 2 ^ 59
def prefixEnd_2132279 : Nat := 4983230072969 + 3 ^ 40 * 2132279 * 2
def baseEnd_2132279 : Nat := 1094884016488368182306333

theorem tailTrace_2132279 : CollatzResearch.WordTrace tailWord_2132279 prefixEnd_2132279 1094884016488368182306333 := by
  unfold tailWord_2132279
  simp only [CollatzResearch.WordTrace]
  refine ⟨77770604242124822105711891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51847069494749881403807927 77770604242124822105711891)
  ·
    refine ⟨116655906363187233158567837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77770604242124822105711891 116655906363187233158567837)
    ·
      refine ⟨43745964886195212434462939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116655906363187233158567837 43745964886195212434462939)
      ·
        refine ⟨65618947329292818651694409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43745964886195212434462939 65618947329292818651694409)
        ·
          refine ⟨49214210496969613988770807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65618947329292818651694409 49214210496969613988770807)
          ·
            refine ⟨73821315745454420983156211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49214210496969613988770807 73821315745454420983156211)
            ·
              refine ⟨110731973618181631474734317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73821315745454420983156211 110731973618181631474734317)
              ·
                refine ⟨41524490106818111803025369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110731973618181631474734317 41524490106818111803025369)
                ·
                  refine ⟨31143367580113583852269027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41524490106818111803025369 31143367580113583852269027)
                  ·
                    refine ⟨46715051370170375778403541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31143367580113583852269027 46715051370170375778403541)
                    ·
                      refine ⟨1094884016488368182306333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 46715051370170375778403541 1094884016488368182306333)
                      ·
                        rfl

theorem cell23_2132279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_2132279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132279 prefixEnd_2132279 := by exact prefixLift 2132279
  have htrace : WordTrace (prefixWord ++ tailWord_2132279) baseStart_2132279 baseEnd_2132279 := by
    simpa [prefixWord, tailWord_2132279, baseEnd_2132279] using wordTrace_append hprefix tailTrace_2132279
  have hstable : (prefixWord ++ tailWord_2132279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132279).length < 2 ^ (prefixWord ++ tailWord_2132279).sum := by decide
  have hdescent : baseEnd_2132279 < baseStart_2132279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132336 : List Nat := [2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 6]
def baseStart_2132336 : Nat := 118140960795 + 2132336 * 2 ^ 59
def prefixEnd_2132336 : Nat := 4983230072969 + 3 ^ 40 * 2132336 * 2
def baseEnd_2132336 : Nat := 1094913284885674459293571

theorem tailTrace_2132336 : CollatzResearch.WordTrace tailWord_2132336 prefixEnd_2132336 1094913284885674459293571 := by
  unfold tailWord_2132336
  simp only [CollatzResearch.WordTrace]
  refine ⟨38886341601459160420268431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51848455468612213893691241 38886341601459160420268431)
  ·
    refine ⟨58329512402188740630402647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38886341601459160420268431 58329512402188740630402647)
    ·
      refine ⟨87494268603283110945603971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58329512402188740630402647 87494268603283110945603971)
      ·
        refine ⟨131241402904924666418405957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87494268603283110945603971 131241402904924666418405957)
        ·
          refine ⟨24607763044673374953451117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 131241402904924666418405957 24607763044673374953451117)
          ·
            refine ⟨9227911141752515607544169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24607763044673374953451117 9227911141752515607544169)
            ·
              refine ⟨6920933356314386705658127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9227911141752515607544169 6920933356314386705658127)
              ·
                refine ⟨10381400034471580058487191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6920933356314386705658127 10381400034471580058487191)
                ·
                  refine ⟨15572100051707370087730787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10381400034471580058487191 15572100051707370087730787)
                  ·
                    refine ⟨23358150077561055131596181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15572100051707370087730787 23358150077561055131596181)
                    ·
                      refine ⟨1094913284885674459293571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23358150077561055131596181 1094913284885674459293571)
                      ·
                        rfl

theorem cell23_2132336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 6].length) (baseStart_2132336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132336 prefixEnd_2132336 := by exact prefixLift 2132336
  have htrace : WordTrace (prefixWord ++ tailWord_2132336) baseStart_2132336 baseEnd_2132336 := by
    simpa [prefixWord, tailWord_2132336, baseEnd_2132336] using wordTrace_append hprefix tailTrace_2132336
  have hstable : (prefixWord ++ tailWord_2132336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132336).length < 2 ^ (prefixWord ++ tailWord_2132336).sum := by decide
  have hdescent : baseEnd_2132336 < baseStart_2132336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132343 : List Nat := [1, 1, 3, 1, 1, 2, 2, 6, 1, 2, 3]
def baseStart_2132343 : Nat := 118140960795 + 2132343 * 2 ^ 59
def prefixEnd_2132343 : Nat := 4983230072969 + 3 ^ 40 * 2132343 * 2
def baseEnd_2132343 : Nat := 1094916879250255931906039

theorem tailTrace_2132343 : CollatzResearch.WordTrace tailWord_2132343 prefixEnd_2132343 1094916879250255931906039 := by
  unfold tailWord_2132343
  simp only [CollatzResearch.WordTrace]
  refine ⟨77772938513892961036041683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51848625675928640690694455 77772938513892961036041683)
  ·
    refine ⟨116659407770839441554062525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77772938513892961036041683 116659407770839441554062525)
    ·
      refine ⟨43747277914064790582773447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116659407770839441554062525 43747277914064790582773447)
      ·
        refine ⟨65620916871097185874160171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43747277914064790582773447 65620916871097185874160171)
        ·
          refine ⟨98431375306645778811240257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65620916871097185874160171 98431375306645778811240257)
          ·
            refine ⟨73823531479984334108430193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98431375306645778811240257 73823531479984334108430193)
            ·
              refine ⟨55367648609988250581322645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73823531479984334108430193 55367648609988250581322645)
              ·
                refine ⟨2595358528593199245999499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 55367648609988250581322645 2595358528593199245999499)
                ·
                  refine ⟨3893037792889798868999249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2595358528593199245999499 3893037792889798868999249)
                  ·
                    refine ⟨2919778344667349151749437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3893037792889798868999249 2919778344667349151749437)
                    ·
                      refine ⟨1094916879250255931906039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2919778344667349151749437 1094916879250255931906039)
                      ·
                        rfl

theorem cell23_2132343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 6, 1, 2, 3].length) (baseStart_2132343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132343 prefixEnd_2132343 := by exact prefixLift 2132343
  have htrace : WordTrace (prefixWord ++ tailWord_2132343) baseStart_2132343 baseEnd_2132343 := by
    simpa [prefixWord, tailWord_2132343, baseEnd_2132343] using wordTrace_append hprefix tailTrace_2132343
  have hstable : (prefixWord ++ tailWord_2132343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132343).length < 2 ^ (prefixWord ++ tailWord_2132343).sum := by decide
  have hdescent : baseEnd_2132343 < baseStart_2132343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132353 : List Nat := [1, 2, 4, 3, 1, 1, 1, 1, 3, 2, 4]
def baseStart_2132353 : Nat := 118140960795 + 2132353 * 2 ^ 59
def prefixEnd_2132353 : Nat := 4983230072969 + 3 ^ 40 * 2132353 * 2
def baseEnd_2132353 : Nat := 1094922014056800892780993

theorem tailTrace_2132353 : CollatzResearch.WordTrace tailWord_2132353 prefixEnd_2132353 1094922014056800892780993 := by
  unfold tailWord_2132353
  simp only [CollatzResearch.WordTrace]
  refine ⟨77773303243856732743905713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51848868829237821829270475 77773303243856732743905713)
  ·
    refine ⟨58329977432892549557929285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77773303243856732743905713 58329977432892549557929285)
    ·
      refine ⟨10936870768667353042111741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58329977432892549557929285 10936870768667353042111741)
      ·
        refine ⟨4101326538250257390791903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10936870768667353042111741 4101326538250257390791903)
        ·
          refine ⟨6151989807375386086187855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4101326538250257390791903 6151989807375386086187855)
          ·
            refine ⟨9227984711063079129281783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6151989807375386086187855 9227984711063079129281783)
            ·
              refine ⟨13841977066594618693922675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9227984711063079129281783 13841977066594618693922675)
              ·
                refine ⟨20762965599891928040884013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13841977066594618693922675 20762965599891928040884013)
                ·
                  refine ⟨7786112099959473015331505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20762965599891928040884013 7786112099959473015331505)
                  ·
                    refine ⟨5839584074969604761498629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7786112099959473015331505 5839584074969604761498629)
                    ·
                      refine ⟨1094922014056800892780993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5839584074969604761498629 1094922014056800892780993)
                      ·
                        rfl

theorem cell23_2132353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_2132353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132353 prefixEnd_2132353 := by exact prefixLift 2132353
  have htrace : WordTrace (prefixWord ++ tailWord_2132353) baseStart_2132353 baseEnd_2132353 := by
    simpa [prefixWord, tailWord_2132353, baseEnd_2132353] using wordTrace_append hprefix tailTrace_2132353
  have hstable : (prefixWord ++ tailWord_2132353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132353).length < 2 ^ (prefixWord ++ tailWord_2132353).sum := by decide
  have hdescent : baseEnd_2132353 < baseStart_2132353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132354 : List Nat := [3, 4, 2, 1, 2, 1, 3, 1, 1, 5]
def baseStart_2132354 : Nat := 118140960795 + 2132354 * 2 ^ 59
def prefixEnd_2132354 : Nat := 4983230072969 + 3 ^ 40 * 2132354 * 2
def baseEnd_2132354 : Nat := 364974175845818462956163

theorem tailTrace_2132354 : CollatzResearch.WordTrace tailWord_2132354 prefixEnd_2132354 364974175845818462956163 := by
  unfold tailWord_2132354
  simp only [CollatzResearch.WordTrace]
  refine ⟨19443334929213277478673029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51848893144568739943128077 19443334929213277478673029)
  ·
    refine ⟨3645625299227489527251193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19443334929213277478673029 3645625299227489527251193)
    ·
      refine ⟨2734218974420617145438395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3645625299227489527251193 2734218974420617145438395)
      ·
        refine ⟨4101328461630925718157593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2734218974420617145438395 4101328461630925718157593)
        ·
          refine ⟨3075996346223194288618195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4101328461630925718157593 3075996346223194288618195)
          ·
            refine ⟨4613994519334791432927293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3075996346223194288618195 4613994519334791432927293)
            ·
              refine ⟨1730247944750546787347735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4613994519334791432927293 1730247944750546787347735)
              ·
                refine ⟨2595371917125820181021603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1730247944750546787347735 2595371917125820181021603)
                ·
                  refine ⟨3893057875688730271532405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2595371917125820181021603 3893057875688730271532405)
                  ·
                    refine ⟨364974175845818462956163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3893057875688730271532405 364974175845818462956163)
                    ·
                      rfl

theorem cell23_2132354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_2132354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132354 prefixEnd_2132354 := by exact prefixLift 2132354
  have htrace : WordTrace (prefixWord ++ tailWord_2132354) baseStart_2132354 baseEnd_2132354 := by
    simpa [prefixWord, tailWord_2132354, baseEnd_2132354] using wordTrace_append hprefix tailTrace_2132354
  have hstable : (prefixWord ++ tailWord_2132354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132354).length < 2 ^ (prefixWord ++ tailWord_2132354).sum := by decide
  have hdescent : baseEnd_2132354 < baseStart_2132354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132357 : List Nat := [1, 3, 1, 1, 3, 1, 1, 7, 1, 2, 2]
def baseStart_2132357 : Nat := 118140960795 + 2132357 * 2 ^ 59
def prefixEnd_2132357 : Nat := 4983230072969 + 3 ^ 40 * 2132357 * 2
def baseEnd_2132357 : Nat := 1094924067979418877130975

theorem tailTrace_2132357 : CollatzResearch.WordTrace tailWord_2132357 prefixEnd_2132357 1094924067979418877130975 := by
  unfold tailWord_2132357
  simp only [CollatzResearch.WordTrace]
  refine ⟨77773449135842241427051325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51848966090561494284700883 77773449135842241427051325)
  ·
    refine ⟨29165043425940840535144247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77773449135842241427051325 29165043425940840535144247)
    ·
      refine ⟨43747565138911260802716371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29165043425940840535144247 43747565138911260802716371)
      ·
        refine ⟨65621347708366891204074557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43747565138911260802716371 65621347708366891204074557)
        ·
          refine ⟨24608005390637584201527959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65621347708366891204074557 24608005390637584201527959)
          ·
            refine ⟨36912008085956376302291939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24608005390637584201527959 36912008085956376302291939)
            ·
              refine ⟨55368012128934564453437909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36912008085956376302291939 55368012128934564453437909)
              ·
                refine ⟨1297687784271903854377451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 55368012128934564453437909 1297687784271903854377451)
                ·
                  refine ⟨1946531676407855781566177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1297687784271903854377451 1946531676407855781566177)
                  ·
                    refine ⟨1459898757305891836174633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1946531676407855781566177 1459898757305891836174633)
                    ·
                      refine ⟨1094924067979418877130975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1459898757305891836174633 1094924067979418877130975)
                      ·
                        rfl

theorem cell23_2132357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 7, 1, 2, 2].length) (baseStart_2132357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132357 prefixEnd_2132357 := by exact prefixLift 2132357
  have htrace : WordTrace (prefixWord ++ tailWord_2132357) baseStart_2132357 baseEnd_2132357 := by
    simpa [prefixWord, tailWord_2132357, baseEnd_2132357] using wordTrace_append hprefix tailTrace_2132357
  have hstable : (prefixWord ++ tailWord_2132357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132357).length < 2 ^ (prefixWord ++ tailWord_2132357).sum := by decide
  have hdescent : baseEnd_2132357 < baseStart_2132357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132396 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 4]
def baseStart_2132396 : Nat := 118140960795 + 2132396 * 2 ^ 59
def prefixEnd_2132396 : Nat := 4983230072969 + 3 ^ 40 * 2132396 * 2
def baseEnd_2132396 : Nat := 1094944093724944224543295

theorem tailTrace_2132396 : CollatzResearch.WordTrace tailWord_2132396 prefixEnd_2132396 1094944093724944224543295 := by
  unfold tailWord_2132396
  simp only [CollatzResearch.WordTrace]
  refine ⟨38887435791350475543860521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51849914388467300725147361 38887435791350475543860521)
  ·
    refine ⟨29165576843512856657895391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38887435791350475543860521 29165576843512856657895391)
    ·
      refine ⟨43748365265269284986843087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29165576843512856657895391 43748365265269284986843087)
      ·
        refine ⟨65622547897903927480264631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43748365265269284986843087 65622547897903927480264631)
        ·
          refine ⟨98433821846855891220396947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65622547897903927480264631 98433821846855891220396947)
          ·
            refine ⟨147650732770283836830595421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98433821846855891220396947 147650732770283836830595421)
            ·
              refine ⟨55369024788856438811473283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 147650732770283836830595421 55369024788856438811473283)
              ·
                refine ⟨83053537183284658217209925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55369024788856438811473283 83053537183284658217209925)
                ·
                  refine ⟨15572538221865873415726861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 83053537183284658217209925 15572538221865873415726861)
                  ·
                    refine ⟨5839701833199702530897573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15572538221865873415726861 5839701833199702530897573)
                    ·
                      refine ⟨1094944093724944224543295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5839701833199702530897573 1094944093724944224543295)
                      ·
                        rfl

theorem cell23_2132396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 4].length) (baseStart_2132396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132396 prefixEnd_2132396 := by exact prefixLift 2132396
  have htrace : WordTrace (prefixWord ++ tailWord_2132396) baseStart_2132396 baseEnd_2132396 := by
    simpa [prefixWord, tailWord_2132396, baseEnd_2132396] using wordTrace_append hprefix tailTrace_2132396
  have hstable : (prefixWord ++ tailWord_2132396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132396).length < 2 ^ (prefixWord ++ tailWord_2132396).sum := by decide
  have hdescent : baseEnd_2132396 < baseStart_2132396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132416 : List Nat := [2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 5]
def baseStart_2132416 : Nat := 118140960795 + 2132416 * 2 ^ 59
def prefixEnd_2132416 : Nat := 4983230072969 + 3 ^ 40 * 2132416 * 2
def baseEnd_2132416 : Nat := 1094954363338034146293203

theorem tailTrace_2132416 : CollatzResearch.WordTrace tailWord_2132416 prefixEnd_2132416 1094954363338034146293203 := by
  unfold tailWord_2132416
  simp only [CollatzResearch.WordTrace]
  refine ⟨38887800521314247251724551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51850400695085663002299401 38887800521314247251724551)
  ·
    refine ⟨58331700781971370877586827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38887800521314247251724551 58331700781971370877586827)
    ·
      refine ⟨87497551172957056316380241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58331700781971370877586827 87497551172957056316380241)
      ·
        refine ⟨65623163379717792237285181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87497551172957056316380241 65623163379717792237285181)
        ·
          refine ⟨24608686267394172088981943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65623163379717792237285181 24608686267394172088981943)
          ·
            refine ⟨36913029401091258133472915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24608686267394172088981943 36913029401091258133472915)
            ·
              refine ⟨55369544101636887200209373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36913029401091258133472915 55369544101636887200209373)
              ·
                refine ⟨20763579038113832700078515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55369544101636887200209373 20763579038113832700078515)
                ·
                  refine ⟨31145368557170749050117773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20763579038113832700078515 31145368557170749050117773)
                  ·
                    refine ⟨11679513208939030893794165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31145368557170749050117773 11679513208939030893794165)
                    ·
                      refine ⟨1094954363338034146293203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11679513208939030893794165 1094954363338034146293203)
                      ·
                        rfl

theorem cell23_2132416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_2132416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132416 prefixEnd_2132416 := by exact prefixLift 2132416
  have htrace : WordTrace (prefixWord ++ tailWord_2132416) baseStart_2132416 baseEnd_2132416 := by
    simpa [prefixWord, tailWord_2132416, baseEnd_2132416] using wordTrace_append hprefix tailTrace_2132416
  have hstable : (prefixWord ++ tailWord_2132416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132416).length < 2 ^ (prefixWord ++ tailWord_2132416).sum := by decide
  have hdescent : baseEnd_2132416 < baseStart_2132416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132447 : List Nat := [1, 1, 2, 3, 3, 4, 1, 1, 1, 4, 2]
def baseStart_2132447 : Nat := 118140960795 + 2132447 * 2 ^ 59
def prefixEnd_2132447 : Nat := 4983230072969 + 3 ^ 40 * 2132447 * 2
def baseEnd_2132447 : Nat := 1094970281238323525005561

theorem tailTrace_2132447 : CollatzResearch.WordTrace tailWord_2132447 prefixEnd_2132447 1094970281238323525005561 := by
  unfold tailWord_2132447
  simp only [CollatzResearch.WordTrace]
  refine ⟨77776731705516186797827595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51851154470344124531885063 77776731705516186797827595)
  ·
    refine ⟨116665097558274280196741393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77776731705516186797827595 116665097558274280196741393)
    ·
      refine ⟨87498823168705710147556045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116665097558274280196741393 87498823168705710147556045)
      ·
        refine ⟨32812058688264641305333517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87498823168705710147556045 32812058688264641305333517)
        ·
          refine ⟨12304522008099240489500069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32812058688264641305333517 12304522008099240489500069)
          ·
            refine ⟨2307097876518607591781263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12304522008099240489500069 2307097876518607591781263)
            ·
              refine ⟨3460646814777911387671895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2307097876518607591781263 3460646814777911387671895)
              ·
                refine ⟨5190970222166867081507843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3460646814777911387671895 5190970222166867081507843)
                ·
                  refine ⟨7786455333250300622261765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5190970222166867081507843 7786455333250300622261765)
                  ·
                    refine ⟨1459960374984431366674081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7786455333250300622261765 1459960374984431366674081)
                    ·
                      refine ⟨1094970281238323525005561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1459960374984431366674081 1094970281238323525005561)
                      ·
                        rfl

theorem cell23_2132447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 4, 2].length) (baseStart_2132447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132447 prefixEnd_2132447 := by exact prefixLift 2132447
  have htrace : WordTrace (prefixWord ++ tailWord_2132447) baseStart_2132447 baseEnd_2132447 := by
    simpa [prefixWord, tailWord_2132447, baseEnd_2132447] using wordTrace_append hprefix tailTrace_2132447
  have hstable : (prefixWord ++ tailWord_2132447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132447).length < 2 ^ (prefixWord ++ tailWord_2132447).sum := by decide
  have hdescent : baseEnd_2132447 < baseStart_2132447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132483 : List Nat := [1, 1, 1, 3, 2, 1, 5, 2, 2, 5]
def baseStart_2132483 : Nat := 118140960795 + 2132483 * 2 ^ 59
def prefixEnd_2132483 : Nat := 4983230072969 + 3 ^ 40 * 2132483 * 2
def baseEnd_2132483 : Nat := 364996255513961794718465

theorem tailTrace_2132483 : CollatzResearch.WordTrace tailWord_2132483 prefixEnd_2132483 364996255513961794718465 := by
  unfold tailWord_2132483
  simp only [CollatzResearch.WordTrace]
  refine ⟨77778044733385764946138103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51852029822257176630758735 77778044733385764946138103)
  ·
    refine ⟨116667067100078647419207155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77778044733385764946138103 116667067100078647419207155)
    ·
      refine ⟨175000600650117971128810733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116667067100078647419207155 175000600650117971128810733)
      ·
        refine ⟨65625225243794239173304025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175000600650117971128810733 65625225243794239173304025)
        ·
          refine ⟨49218918932845679379978019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65625225243794239173304025 49218918932845679379978019)
          ·
            refine ⟨73828378399268519069967029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49218918932845679379978019 73828378399268519069967029)
            ·
              refine ⟨6921410474931423662809409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 73828378399268519069967029 6921410474931423662809409)
              ·
                refine ⟨5191057856198567747107057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6921410474931423662809409 5191057856198567747107057)
                ·
                  refine ⟨3893293392148925810330293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5191057856198567747107057 3893293392148925810330293)
                  ·
                    refine ⟨364996255513961794718465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3893293392148925810330293 364996255513961794718465)
                    ·
                      rfl

theorem cell23_2132483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 2, 5].length) (baseStart_2132483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132483 prefixEnd_2132483 := by exact prefixLift 2132483
  have htrace : WordTrace (prefixWord ++ tailWord_2132483) baseStart_2132483 baseEnd_2132483 := by
    simpa [prefixWord, tailWord_2132483, baseEnd_2132483] using wordTrace_append hprefix tailTrace_2132483
  have hstable : (prefixWord ++ tailWord_2132483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132483).length < 2 ^ (prefixWord ++ tailWord_2132483).sum := by decide
  have hdescent : baseEnd_2132483 < baseStart_2132483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132487 : List Nat := [1, 1, 4, 3, 4, 1, 1, 1, 7]
def baseStart_2132487 : Nat := 118140960795 + 2132487 * 2 ^ 59
def prefixEnd_2132487 : Nat := 4983230072969 + 3 ^ 40 * 2132487 * 2
def baseEnd_2132487 : Nat := 121665646718278152056153

theorem tailTrace_2132487 : CollatzResearch.WordTrace tailWord_2132487 prefixEnd_2132487 121665646718278152056153 := by
  unfold tailWord_2132487
  simp only [CollatzResearch.WordTrace]
  refine ⟨77778190625371273629283715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51852127083580849086189143 77778190625371273629283715)
  ·
    refine ⟨116667285938056910443925573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77778190625371273629283715 116667285938056910443925573)
    ·
      refine ⟨21875116113385670708236045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116667285938056910443925573 21875116113385670708236045)
      ·
        refine ⟨8203168542519626515588517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21875116113385670708236045 8203168542519626515588517)
        ·
          refine ⟨1538094101722429971672847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8203168542519626515588517 1538094101722429971672847)
          ·
            refine ⟨2307141152583644957509271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1538094101722429971672847 2307141152583644957509271)
            ·
              refine ⟨3460711728875467436263907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2307141152583644957509271 3460711728875467436263907)
              ·
                refine ⟨5191067593313201154395861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3460711728875467436263907 5191067593313201154395861)
                ·
                  refine ⟨121665646718278152056153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5191067593313201154395861 121665646718278152056153)
                  ·
                    rfl

theorem cell23_2132487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 7].length) (baseStart_2132487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132487 prefixEnd_2132487 := by exact prefixLift 2132487
  have htrace : WordTrace (prefixWord ++ tailWord_2132487) baseStart_2132487 baseEnd_2132487 := by
    simpa [prefixWord, tailWord_2132487, baseEnd_2132487] using wordTrace_append hprefix tailTrace_2132487
  have hstable : (prefixWord ++ tailWord_2132487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132487).length < 2 ^ (prefixWord ++ tailWord_2132487).sum := by decide
  have hdescent : baseEnd_2132487 < baseStart_2132487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132490 : List Nat := [3, 1, 2, 2, 2, 1, 2, 1, 2, 5, 2]
def baseStart_2132490 : Nat := 118140960795 + 2132490 * 2 ^ 59
def prefixEnd_2132490 : Nat := 4983230072969 + 3 ^ 40 * 2132490 * 2
def baseEnd_2132490 : Nat := 1094992360906466856767863

theorem tailTrace_2132490 : CollatzResearch.WordTrace tailWord_2132490 prefixEnd_2132490 1094992360906466856767863 := by
  unfold tailWord_2132490
  simp only [CollatzResearch.WordTrace]
  refine ⟨19444575011090101285410731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51852200029573603427761949 19444575011090101285410731)
  ·
    refine ⟨29166862516635151928116097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19444575011090101285410731 29166862516635151928116097)
    ·
      refine ⟨21875146887476363946087073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29166862516635151928116097 21875146887476363946087073)
      ·
        refine ⟨16406360165607272959565305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21875146887476363946087073 16406360165607272959565305)
        ·
          refine ⟨12304770124205454719673979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16406360165607272959565305 12304770124205454719673979)
          ·
            refine ⟨18457155186308182079510969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12304770124205454719673979 18457155186308182079510969)
            ·
              refine ⟨13842866389731136559633227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18457155186308182079510969 13842866389731136559633227)
              ·
                refine ⟨20764299584596704839449841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13842866389731136559633227 20764299584596704839449841)
                ·
                  refine ⟨15573224688447528629587381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20764299584596704839449841 15573224688447528629587381)
                  ·
                    refine ⟨1459989814541955809023817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15573224688447528629587381 1459989814541955809023817)
                    ·
                      refine ⟨1094992360906466856767863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1459989814541955809023817 1094992360906466856767863)
                      ·
                        rfl

theorem cell23_2132490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 2, 5, 2].length) (baseStart_2132490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132490 prefixEnd_2132490 := by exact prefixLift 2132490
  have htrace : WordTrace (prefixWord ++ tailWord_2132490) baseStart_2132490 baseEnd_2132490 := by
    simpa [prefixWord, tailWord_2132490, baseEnd_2132490] using wordTrace_append hprefix tailTrace_2132490
  have hstable : (prefixWord ++ tailWord_2132490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132490).length < 2 ^ (prefixWord ++ tailWord_2132490).sum := by decide
  have hdescent : baseEnd_2132490 < baseStart_2132490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132496 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 3, 10]
def baseStart_2132496 : Nat := 118140960795 + 2132496 * 2 ^ 59
def prefixEnd_2132496 : Nat := 4983230072969 + 3 ^ 40 * 2132496 * 2
def baseEnd_2132496 : Nat := 364998480596797944430945

theorem tailTrace_2132496 : CollatzResearch.WordTrace tailWord_2132496 prefixEnd_2132496 364998480596797944430945 := by
  unfold tailWord_2132496
  simp only [CollatzResearch.WordTrace]
  refine ⟨38889259441169334083180671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51852345921559112110907561 38889259441169334083180671)
  ·
    refine ⟨58333889161754001124771007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38889259441169334083180671 58333889161754001124771007)
    ·
      refine ⟨87500833742631001687156511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58333889161754001124771007 87500833742631001687156511)
      ·
        refine ⟨131251250613946502530734767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87500833742631001687156511 131251250613946502530734767)
        ·
          refine ⟨196876875920919753796102151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131251250613946502530734767 196876875920919753796102151)
          ·
            refine ⟨295315313881379630694153227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196876875920919753796102151 295315313881379630694153227)
            ·
              refine ⟨442972970822069446041229841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295315313881379630694153227 442972970822069446041229841)
              ·
                refine ⟨332229728116552084530922381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 442972970822069446041229841 332229728116552084530922381)
                ·
                  refine ⟨124586148043707031699095893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 332229728116552084530922381 124586148043707031699095893)
                  ·
                    refine ⟨364998480596797944430945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 124586148043707031699095893 364998480596797944430945)
                    ·
                      rfl

theorem cell23_2132496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 3, 10].length) (baseStart_2132496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132496 prefixEnd_2132496 := by exact prefixLift 2132496
  have htrace : WordTrace (prefixWord ++ tailWord_2132496) baseStart_2132496 baseEnd_2132496 := by
    simpa [prefixWord, tailWord_2132496, baseEnd_2132496] using wordTrace_append hprefix tailTrace_2132496
  have hstable : (prefixWord ++ tailWord_2132496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132496).length < 2 ^ (prefixWord ++ tailWord_2132496).sum := by decide
  have hdescent : baseEnd_2132496 < baseStart_2132496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132523 : List Nat := [1, 1, 1, 1, 2, 1, 3, 5, 1, 4, 3]
def baseStart_2132523 : Nat := 118140960795 + 2132523 * 2 ^ 59
def prefixEnd_2132523 : Nat := 4983230072969 + 3 ^ 40 * 2132523 * 2
def baseEnd_2132523 : Nat := 1095009305768065227655211

theorem tailTrace_2132523 : CollatzResearch.WordTrace tailWord_2132523 prefixEnd_2132523 1095009305768065227655211 := by
  unfold tailWord_2132523
  simp only [CollatzResearch.WordTrace]
  refine ⟨77779503653240851777594223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51853002435493901185062815 77779503653240851777594223)
  ·
    refine ⟨116669255479861277666391335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77779503653240851777594223 116669255479861277666391335)
    ·
      refine ⟨175003883219791916499587003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116669255479861277666391335 175003883219791916499587003)
      ·
        refine ⟨262505824829687874749380505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175003883219791916499587003 262505824829687874749380505)
        ·
          refine ⟨196879368622265906062035379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 262505824829687874749380505 196879368622265906062035379)
          ·
            refine ⟨295319052933398859093053069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196879368622265906062035379 295319052933398859093053069)
            ·
              refine ⟨110744644850024572159894901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 295319052933398859093053069 110744644850024572159894901)
              ·
                refine ⟨10382310454689803639990147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 110744644850024572159894901 10382310454689803639990147)
                ·
                  refine ⟨15573465682034705459985221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10382310454689803639990147 15573465682034705459985221)
                  ·
                    refine ⟨2920024815381507273747229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15573465682034705459985221 2920024815381507273747229)
                    ·
                      refine ⟨1095009305768065227655211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2920024815381507273747229 1095009305768065227655211)
                      ·
                        rfl

theorem cell23_2132523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 4, 3].length) (baseStart_2132523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132523 prefixEnd_2132523 := by exact prefixLift 2132523
  have htrace : WordTrace (prefixWord ++ tailWord_2132523) baseStart_2132523 baseEnd_2132523 := by
    simpa [prefixWord, tailWord_2132523, baseEnd_2132523] using wordTrace_append hprefix tailTrace_2132523
  have hstable : (prefixWord ++ tailWord_2132523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132523).length < 2 ^ (prefixWord ++ tailWord_2132523).sum := by decide
  have hdescent : baseEnd_2132523 < baseStart_2132523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132533 : List Nat := [1, 3, 3, 1, 1, 2, 2, 1, 2, 1, 6]
def baseStart_2132533 : Nat := 118140960795 + 2132533 * 2 ^ 59
def prefixEnd_2132533 : Nat := 4983230072969 + 3 ^ 40 * 2132533 * 2
def baseEnd_2132533 : Nat := 1095014440574610188530165

theorem tailTrace_2132533 : CollatzResearch.WordTrace tailWord_2132533 prefixEnd_2132533 1095014440574610188530165 := by
  unfold tailWord_2132533
  simp only [CollatzResearch.WordTrace]
  refine ⟨77779868383204623485458253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51853245588803082323638835 77779868383204623485458253)
  ·
    refine ⟨29167450643701733807046845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77779868383204623485458253 29167450643701733807046845)
    ·
      refine ⟨10937793991388150177642567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29167450643701733807046845 10937793991388150177642567)
      ·
        refine ⟨16406690987082225266463851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10937793991388150177642567 16406690987082225266463851)
        ·
          refine ⟨24610036480623337899695777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16406690987082225266463851 24610036480623337899695777)
          ·
            refine ⟨18457527360467503424771833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24610036480623337899695777 18457527360467503424771833)
            ·
              refine ⟨13843145520350627568578875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18457527360467503424771833 13843145520350627568578875)
              ·
                refine ⟨20764718280525941352868313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13843145520350627568578875 20764718280525941352868313)
                ·
                  refine ⟨15573538710394456014651235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20764718280525941352868313 15573538710394456014651235)
                  ·
                    refine ⟨23360308065591684021976853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15573538710394456014651235 23360308065591684021976853)
                    ·
                      refine ⟨1095014440574610188530165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23360308065591684021976853 1095014440574610188530165)
                      ·
                        rfl

theorem cell23_2132533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_2132533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132533 prefixEnd_2132533 := by exact prefixLift 2132533
  have htrace : WordTrace (prefixWord ++ tailWord_2132533) baseStart_2132533 baseEnd_2132533 := by
    simpa [prefixWord, tailWord_2132533, baseEnd_2132533] using wordTrace_append hprefix tailTrace_2132533
  have hstable : (prefixWord ++ tailWord_2132533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132533).length < 2 ^ (prefixWord ++ tailWord_2132533).sum := by decide
  have hdescent : baseEnd_2132533 < baseStart_2132533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132553 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 4, 5, 3]
def baseStart_2132553 : Nat := 118140960795 + 2132553 * 2 ^ 59
def prefixEnd_2132553 : Nat := 4983230072969 + 3 ^ 40 * 2132553 * 2
def baseEnd_2132553 : Nat := 1095024710187700110280073

theorem tailTrace_2132553 : CollatzResearch.WordTrace tailWord_2132553 prefixEnd_2132553 1095024710187700110280073 := by
  unfold tailWord_2132553
  simp only [CollatzResearch.WordTrace]
  refine ⟨77780597843132166901186313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51853731895421444600790875 77780597843132166901186313)
  ·
    refine ⟨58335448382349125175889735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77780597843132166901186313 58335448382349125175889735)
    ·
      refine ⟨87503172573523687763834603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58335448382349125175889735 87503172573523687763834603)
      ·
        refine ⟨131254758860285531645751905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87503172573523687763834603 131254758860285531645751905)
        ·
          refine ⟨98441069145214148734313929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131254758860285531645751905 98441069145214148734313929)
          ·
            refine ⟨73830801858910611550735447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98441069145214148734313929 73830801858910611550735447)
            ·
              refine ⟨110746202788365917326103171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73830801858910611550735447 110746202788365917326103171)
              ·
                refine ⟨166119304182548875989154757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110746202788365917326103171 166119304182548875989154757)
                ·
                  refine ⟨31147369534227914247966517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 166119304182548875989154757 31147369534227914247966517)
                  ·
                    refine ⟨2920065893833866960746861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31147369534227914247966517 2920065893833866960746861)
                    ·
                      refine ⟨1095024710187700110280073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2920065893833866960746861 1095024710187700110280073)
                      ·
                        rfl

theorem cell23_2132553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 5, 3].length) (baseStart_2132553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132553 prefixEnd_2132553 := by exact prefixLift 2132553
  have htrace : WordTrace (prefixWord ++ tailWord_2132553) baseStart_2132553 baseEnd_2132553 := by
    simpa [prefixWord, tailWord_2132553, baseEnd_2132553] using wordTrace_append hprefix tailTrace_2132553
  have hstable : (prefixWord ++ tailWord_2132553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132553).length < 2 ^ (prefixWord ++ tailWord_2132553).sum := by decide
  have hdescent : baseEnd_2132553 < baseStart_2132553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132583 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 5]
def baseStart_2132583 : Nat := 118140960795 + 2132583 * 2 ^ 59
def prefixEnd_2132583 : Nat := 4983230072969 + 3 ^ 40 * 2132583 * 2
def baseEnd_2132583 : Nat := 1095040114607334992904935

theorem tailTrace_2132583 : CollatzResearch.WordTrace tailWord_2132583 prefixEnd_2132583 1095040114607334992904935 := by
  unfold tailWord_2132583
  simp only [CollatzResearch.WordTrace]
  refine ⟨77781692033023482024778403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51854461355348988016518935 77781692033023482024778403)
  ·
    refine ⟨116672538049535223037167605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77781692033023482024778403 116672538049535223037167605)
    ·
      refine ⟨10938050442143927159734463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 116672538049535223037167605 10938050442143927159734463)
      ·
        refine ⟨16407075663215890739601695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10938050442143927159734463 16407075663215890739601695)
        ·
          refine ⟨24610613494823836109402543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16407075663215890739601695 24610613494823836109402543)
          ·
            refine ⟨36915920242235754164103815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24610613494823836109402543 36915920242235754164103815)
            ·
              refine ⟨55373880363353631246155723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36915920242235754164103815 55373880363353631246155723)
              ·
                refine ⟨83060820545030446869233585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55373880363353631246155723 83060820545030446869233585)
                ·
                  refine ⟨62295615408772835151925189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83060820545030446869233585 62295615408772835151925189)
                  ·
                    refine ⟨11680427889144906590985973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62295615408772835151925189 11680427889144906590985973)
                    ·
                      refine ⟨1095040114607334992904935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11680427889144906590985973 1095040114607334992904935)
                      ·
                        rfl

theorem cell23_2132583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_2132583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132583 prefixEnd_2132583 := by exact prefixLift 2132583
  have htrace : WordTrace (prefixWord ++ tailWord_2132583) baseStart_2132583 baseEnd_2132583 := by
    simpa [prefixWord, tailWord_2132583, baseEnd_2132583] using wordTrace_append hprefix tailTrace_2132583
  have hstable : (prefixWord ++ tailWord_2132583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132583).length < 2 ^ (prefixWord ++ tailWord_2132583).sum := by decide
  have hdescent : baseEnd_2132583 < baseStart_2132583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132594 : List Nat := [3, 2, 1, 2, 5, 1, 1, 2, 6]
def baseStart_2132594 : Nat := 118140960795 + 2132594 * 2 ^ 59
def prefixEnd_2132594 : Nat := 4983230072969 + 3 ^ 40 * 2132594 * 2
def baseEnd_2132594 : Nat := 121671751432726049985265

theorem tailTrace_2132594 : CollatzResearch.WordTrace tailWord_2132594 prefixEnd_2132594 121671751432726049985265 := by
  unfold tailWord_2132594
  simp only [CollatzResearch.WordTrace]
  refine ⟨19445523308995907725857209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51854728823989087268952557 19445523308995907725857209)
  ·
    refine ⟨14584142481746930794392907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19445523308995907725857209 14584142481746930794392907)
    ·
      refine ⟨21876213722620396191589361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14584142481746930794392907 21876213722620396191589361)
      ·
        refine ⟨16407160291965297143692021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21876213722620396191589361 16407160291965297143692021)
        ·
          refine ⟨1538171277371746607221127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16407160291965297143692021 1538171277371746607221127)
          ·
            refine ⟨2307256916057619910831691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1538171277371746607221127 2307256916057619910831691)
            ·
              refine ⟨3460885374086429866247537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2307256916057619910831691 3460885374086429866247537)
              ·
                refine ⟨2595664030564822399685653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3460885374086429866247537 2595664030564822399685653)
                ·
                  refine ⟨121671751432726049985265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2595664030564822399685653 121671751432726049985265)
                  ·
                    rfl

theorem cell23_2132594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 2, 6].length) (baseStart_2132594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132594 prefixEnd_2132594 := by exact prefixLift 2132594
  have htrace : WordTrace (prefixWord ++ tailWord_2132594) baseStart_2132594 baseEnd_2132594 := by
    simpa [prefixWord, tailWord_2132594, baseEnd_2132594] using wordTrace_append hprefix tailTrace_2132594
  have hstable : (prefixWord ++ tailWord_2132594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132594).length < 2 ^ (prefixWord ++ tailWord_2132594).sum := by decide
  have hdescent : baseEnd_2132594 < baseStart_2132594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132604 : List Nat := [2, 2, 2, 1, 1, 2, 4, 4, 1, 1, 3]
def baseStart_2132604 : Nat := 118140960795 + 2132604 * 2 ^ 59
def prefixEnd_2132604 : Nat := 4983230072969 + 3 ^ 40 * 2132604 * 2
def baseEnd_2132604 : Nat := 1095050897701079410742339

theorem tailTrace_2132604 : CollatzResearch.WordTrace tailWord_2132604 prefixEnd_2132604 1095050897701079410742339 := by
  unfold tailWord_2132604
  simp only [CollatzResearch.WordTrace]
  refine ⟨38891228982973701305646433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51854971977298268407528577 38891228982973701305646433)
  ·
    refine ⟨29168421737230275979234825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38891228982973701305646433 29168421737230275979234825)
    ·
      refine ⟨21876316302922706984426119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29168421737230275979234825 21876316302922706984426119)
      ·
        refine ⟨32814474454384060476639179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21876316302922706984426119 32814474454384060476639179)
        ·
          refine ⟨49221711681576090714958769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32814474454384060476639179 49221711681576090714958769)
          ·
            refine ⟨36916283761182068036219077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49221711681576090714958769 36916283761182068036219077)
            ·
              refine ⟨6921803205221637756791077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36916283761182068036219077 6921803205221637756791077)
              ·
                refine ⟨1297838100979057079398327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6921803205221637756791077 1297838100979057079398327)
                ·
                  refine ⟨1946757151468585619097491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1297838100979057079398327 1946757151468585619097491)
                  ·
                    refine ⟨2920135727202878428646237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1946757151468585619097491 2920135727202878428646237)
                    ·
                      refine ⟨1095050897701079410742339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2920135727202878428646237 1095050897701079410742339)
                      ·
                        rfl

theorem cell23_2132604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 4, 1, 1, 3].length) (baseStart_2132604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132604 prefixEnd_2132604 := by exact prefixLift 2132604
  have htrace : WordTrace (prefixWord ++ tailWord_2132604) baseStart_2132604 baseEnd_2132604 := by
    simpa [prefixWord, tailWord_2132604, baseEnd_2132604] using wordTrace_append hprefix tailTrace_2132604
  have hstable : (prefixWord ++ tailWord_2132604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132604).length < 2 ^ (prefixWord ++ tailWord_2132604).sum := by decide
  have hdescent : baseEnd_2132604 < baseStart_2132604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132623 : List Nat := [1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 6]
def baseStart_2132623 : Nat := 118140960795 + 2132623 * 2 ^ 59
def prefixEnd_2132623 : Nat := 4983230072969 + 3 ^ 40 * 2132623 * 2
def baseEnd_2132623 : Nat := 1095060653833514836404751

theorem tailTrace_2132623 : CollatzResearch.WordTrace tailWord_2132623 prefixEnd_2132623 1095060653833514836404751 := by
  unfold tailWord_2132623
  simp only [CollatzResearch.WordTrace]
  refine ⟨77783150952878568856234523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51855433968585712570823015 77783150952878568856234523)
  ·
    refine ⟨116674726429317853284351785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77783150952878568856234523 116674726429317853284351785)
    ·
      refine ⟨87506044821988389963263839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116674726429317853284351785 87506044821988389963263839)
      ·
        refine ⟨131259067232982584944895759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87506044821988389963263839 131259067232982584944895759)
        ·
          refine ⟨196888600849473877417343639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131259067232982584944895759 196888600849473877417343639)
          ·
            refine ⟨295332901274210816126015459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196888600849473877417343639 295332901274210816126015459)
            ·
              refine ⟨442999351911316224189023189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295332901274210816126015459 442999351911316224189023189)
              ·
                refine ⟨10382797310421474004430231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 442999351911316224189023189 10382797310421474004430231)
                ·
                  refine ⟨15574195965632211006645347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10382797310421474004430231 15574195965632211006645347)
                  ·
                    refine ⟨23361293948448316509968021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15574195965632211006645347 23361293948448316509968021)
                    ·
                      refine ⟨1095060653833514836404751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23361293948448316509968021 1095060653833514836404751)
                      ·
                        rfl

theorem cell23_2132623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 6].length) (baseStart_2132623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132623 prefixEnd_2132623 := by exact prefixLift 2132623
  have htrace : WordTrace (prefixWord ++ tailWord_2132623) baseStart_2132623 baseEnd_2132623 := by
    simpa [prefixWord, tailWord_2132623, baseEnd_2132623] using wordTrace_append hprefix tailTrace_2132623
  have hstable : (prefixWord ++ tailWord_2132623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132623).length < 2 ^ (prefixWord ++ tailWord_2132623).sum := by decide
  have hdescent : baseEnd_2132623 < baseStart_2132623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132633 : List Nat := [1, 2, 1, 2, 1, 2, 5, 9]
def baseStart_2132633 : Nat := 118140960795 + 2132633 * 2 ^ 59
def prefixEnd_2132633 : Nat := 4983230072969 + 3 ^ 40 * 2132633 * 2
def baseEnd_2132633 : Nat := 40557992171854066565915

theorem tailTrace_2132633 : CollatzResearch.WordTrace tailWord_2132633 prefixEnd_2132633 40557992171854066565915 := by
  unfold tailWord_2132633
  simp only [CollatzResearch.WordTrace]
  refine ⟨77783515682842340564098553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51855677121894893709399035 77783515682842340564098553)
  ·
    refine ⟨58337636762131755423073915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77783515682842340564098553 58337636762131755423073915)
    ·
      refine ⟨87506455143197633134610873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58337636762131755423073915 87506455143197633134610873)
      ·
        refine ⟨65629841357398224850958155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87506455143197633134610873 65629841357398224850958155)
        ·
          refine ⟨98444762036097337276437233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65629841357398224850958155 98444762036097337276437233)
          ·
            refine ⟨73833571527073002957327925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98444762036097337276437233 73833571527073002957327925)
            ·
              refine ⟨6921897330663094027249493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 73833571527073002957327925 6921897330663094027249493)
              ·
                refine ⟨40557992171854066565915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6921897330663094027249493 40557992171854066565915)
                ·
                  rfl

theorem cell23_2132633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 9].length) (baseStart_2132633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132633 prefixEnd_2132633 := by exact prefixLift 2132633
  have htrace : WordTrace (prefixWord ++ tailWord_2132633) baseStart_2132633 baseEnd_2132633 := by
    simpa [prefixWord, tailWord_2132633, baseEnd_2132633] using wordTrace_append hprefix tailTrace_2132633
  have hstable : (prefixWord ++ tailWord_2132633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132633).length < 2 ^ (prefixWord ++ tailWord_2132633).sum := by decide
  have hdescent : baseEnd_2132633 < baseStart_2132633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132654 : List Nat := [4, 1, 4, 1, 1, 1, 2, 1, 4, 4]
def baseStart_2132654 : Nat := 118140960795 + 2132654 * 2 ^ 59
def prefixEnd_2132654 : Nat := 4983230072969 + 3 ^ 40 * 2132654 * 2
def baseEnd_2132654 : Nat := 365025523911268071705703

theorem tailTrace_2132654 : CollatzResearch.WordTrace tailWord_2132654 prefixEnd_2132654 365025523911268071705703 := by
  unfold tailWord_2132654
  simp only [CollatzResearch.WordTrace]
  refine ⟨9723035201970782643826627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51856187743844174100408677 9723035201970782643826627)
  ·
    refine ⟨14584552802956173965739941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9723035201970782643826627 14584552802956173965739941)
    ·
      refine ⟨2734603650554282618576239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14584552802956173965739941 2734603650554282618576239)
      ·
        refine ⟨4101905475831423927864359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2734603650554282618576239 4101905475831423927864359)
        ·
          refine ⟨6152858213747135891796539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4101905475831423927864359 6152858213747135891796539)
          ·
            refine ⟨9229287320620703837694809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6152858213747135891796539 9229287320620703837694809)
            ·
              refine ⟨6921965490465527878271107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9229287320620703837694809 6921965490465527878271107)
              ·
                refine ⟨10382948235698291817406661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6921965490465527878271107 10382948235698291817406661)
                ·
                  refine ⟨1946802794193429715763749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10382948235698291817406661 1946802794193429715763749)
                  ·
                    refine ⟨365025523911268071705703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1946802794193429715763749 365025523911268071705703)
                    ·
                      rfl

theorem cell23_2132654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_2132654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132654 prefixEnd_2132654 := by exact prefixLift 2132654
  have htrace : WordTrace (prefixWord ++ tailWord_2132654) baseStart_2132654 baseEnd_2132654 := by
    simpa [prefixWord, tailWord_2132654, baseEnd_2132654] using wordTrace_append hprefix tailTrace_2132654
  have hstable : (prefixWord ++ tailWord_2132654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132654).length < 2 ^ (prefixWord ++ tailWord_2132654).sum := by decide
  have hdescent : baseEnd_2132654 < baseStart_2132654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132661 : List Nat := [1, 3, 3, 3, 1, 1, 3, 1, 3, 2, 2]
def baseStart_2132661 : Nat := 118140960795 + 2132661 * 2 ^ 59
def prefixEnd_2132661 : Nat := 4983230072969 + 3 ^ 40 * 2132661 * 2
def baseEnd_2132661 : Nat := 1095080166098385687729577

theorem tailTrace_2132661 : CollatzResearch.WordTrace tailWord_2132661 prefixEnd_2132661 1095080166098385687729577 := by
  unfold tailWord_2132661
  simp only [CollatzResearch.WordTrace]
  refine ⟨77784536926740901346117837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51856357951160600897411891 77784536926740901346117837)
  ·
    refine ⟨29169201347527838004794189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77784536926740901346117837 29169201347527838004794189)
    ·
      refine ⟨10938450505322939251797821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29169201347527838004794189 10938450505322939251797821)
      ·
        refine ⟨4101918939496102219424183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10938450505322939251797821 4101918939496102219424183)
        ·
          refine ⟨6152878409244153329136275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4101918939496102219424183 6152878409244153329136275)
          ·
            refine ⟨9229317613866229993704413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6152878409244153329136275 9229317613866229993704413)
            ·
              refine ⟨3460994105199836247639155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9229317613866229993704413 3460994105199836247639155)
              ·
                refine ⟨5191491157799754371458733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3460994105199836247639155 5191491157799754371458733)
                ·
                  refine ⟨1946809184174907889297025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5191491157799754371458733 1946809184174907889297025)
                  ·
                    refine ⟨1460106888131180916972769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1946809184174907889297025 1460106888131180916972769)
                    ·
                      refine ⟨1095080166098385687729577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1460106888131180916972769 1095080166098385687729577)
                      ·
                        rfl

theorem cell23_2132661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_2132661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132661 prefixEnd_2132661 := by exact prefixLift 2132661
  have htrace : WordTrace (prefixWord ++ tailWord_2132661) baseStart_2132661 baseEnd_2132661 := by
    simpa [prefixWord, tailWord_2132661, baseEnd_2132661] using wordTrace_append hprefix tailTrace_2132661
  have hstable : (prefixWord ++ tailWord_2132661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132661).length < 2 ^ (prefixWord ++ tailWord_2132661).sum := by decide
  have hdescent : baseEnd_2132661 < baseStart_2132661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132670 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6]
def baseStart_2132670 : Nat := 118140960795 + 2132670 * 2 ^ 59
def prefixEnd_2132670 : Nat := 4983230072969 + 3 ^ 40 * 2132670 * 2
def baseEnd_2132670 : Nat := 1095084787424276152517035

theorem tailTrace_2132670 : CollatzResearch.WordTrace tailWord_2132670 prefixEnd_2132670 1095084787424276152517035 := by
  unfold tailWord_2132670
  simp only [CollatzResearch.WordTrace]
  refine ⟨9723108147963536985399433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51856576789138863922130309 9723108147963536985399433)
  ·
    refine ⟨7292331110972652739049575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9723108147963536985399433 7292331110972652739049575)
    ·
      refine ⟨10938496666458979108574363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7292331110972652739049575 10938496666458979108574363)
      ·
        refine ⟨16407744999688468662861545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10938496666458979108574363 16407744999688468662861545)
        ·
          refine ⟨12305808749766351497146159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16407744999688468662861545 12305808749766351497146159)
          ·
            refine ⟨18458713124649527245719239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12305808749766351497146159 18458713124649527245719239)
            ·
              refine ⟨27688069686974290868578859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18458713124649527245719239 27688069686974290868578859)
              ·
                refine ⟨41532104530461436302868289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27688069686974290868578859 41532104530461436302868289)
                ·
                  refine ⟨31149078397846077227151217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41532104530461436302868289 31149078397846077227151217)
                  ·
                    refine ⟨23361808798384557920363413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31149078397846077227151217 23361808798384557920363413)
                    ·
                      refine ⟨1095084787424276152517035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23361808798384557920363413 1095084787424276152517035)
                      ·
                        rfl

theorem cell23_2132670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_2132670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132670 prefixEnd_2132670 := by exact prefixLift 2132670
  have htrace : WordTrace (prefixWord ++ tailWord_2132670) baseStart_2132670 baseEnd_2132670 := by
    simpa [prefixWord, tailWord_2132670, baseEnd_2132670] using wordTrace_append hprefix tailTrace_2132670
  have hstable : (prefixWord ++ tailWord_2132670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132670).length < 2 ^ (prefixWord ++ tailWord_2132670).sum := by decide
  have hdescent : baseEnd_2132670 < baseStart_2132670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132683 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 10]
def baseStart_2132683 : Nat := 118140960795 + 2132683 * 2 ^ 59
def prefixEnd_2132683 : Nat := 4983230072969 + 3 ^ 40 * 2132683 * 2
def baseEnd_2132683 : Nat := 1095091462672784601654475

theorem tailTrace_2132683 : CollatzResearch.WordTrace tailWord_2132683 prefixEnd_2132683 1095091462672784601654475 := by
  unfold tailWord_2132683
  simp only [CollatzResearch.WordTrace]
  refine ⟨77785339332661199103418703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51856892888440799402279135 77785339332661199103418703)
  ·
    refine ⟨116678008998991798655128055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77785339332661199103418703 116678008998991798655128055)
    ·
      refine ⟨175017013498487697982692083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116678008998991798655128055 175017013498487697982692083)
      ·
        refine ⟨262525520247731546974038125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175017013498487697982692083 262525520247731546974038125)
        ·
          refine ⟨98447070092899330115264297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 262525520247731546974038125 98447070092899330115264297)
          ·
            refine ⟨73835302569674497586448223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98447070092899330115264297 73835302569674497586448223)
            ·
              refine ⟨110752953854511746379672335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73835302569674497586448223 110752953854511746379672335)
              ·
                refine ⟨166129430781767619569508503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110752953854511746379672335 166129430781767619569508503)
                ·
                  refine ⟨249194146172651429354262755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 166129430781767619569508503 249194146172651429354262755)
                  ·
                    refine ⟨373791219258977144031394133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 249194146172651429354262755 373791219258977144031394133)
                    ·
                      refine ⟨1095091462672784601654475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 373791219258977144031394133 1095091462672784601654475)
                      ·
                        rfl

theorem cell23_2132683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 10].length) (baseStart_2132683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132683 prefixEnd_2132683 := by exact prefixLift 2132683
  have htrace : WordTrace (prefixWord ++ tailWord_2132683) baseStart_2132683 baseEnd_2132683 := by
    simpa [prefixWord, tailWord_2132683, baseEnd_2132683] using wordTrace_append hprefix tailTrace_2132683
  have hstable : (prefixWord ++ tailWord_2132683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132683).length < 2 ^ (prefixWord ++ tailWord_2132683).sum := by decide
  have hdescent : baseEnd_2132683 < baseStart_2132683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132712 : List Nat := [2, 1, 4, 1, 5, 1, 2, 2, 1, 2, 2]
def baseStart_2132712 : Nat := 118140960795 + 2132712 * 2 ^ 59
def prefixEnd_2132712 : Nat := 4983230072969 + 3 ^ 40 * 2132712 * 2
def baseEnd_2132712 : Nat := 1095106353611764988191843

theorem tailTrace_2132712 : CollatzResearch.WordTrace tailWord_2132712 prefixEnd_2132712 1095106353611764988191843 := by
  unfold tailWord_2132712
  simp only [CollatzResearch.WordTrace]
  refine ⟨38893198524778068528112195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51857598033037424704149593 38893198524778068528112195)
  ·
    refine ⟨58339797787167102792168293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38893198524778068528112195 58339797787167102792168293)
    ·
      refine ⟨10938712085093831773531555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58339797787167102792168293 10938712085093831773531555)
      ·
        refine ⟨16408068127640747660297333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10938712085093831773531555 16408068127640747660297333)
        ·
          refine ⟨1538256386966320093152875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16408068127640747660297333 1538256386966320093152875)
          ·
            refine ⟨2307384580449480139729313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1538256386966320093152875 2307384580449480139729313)
            ·
              refine ⟨1730538435337110104796985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2307384580449480139729313 1730538435337110104796985)
              ·
                refine ⟨1297903826502832578597739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1730538435337110104796985 1297903826502832578597739)
                ·
                  refine ⟨1946855739754248867896609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1297903826502832578597739 1946855739754248867896609)
                  ·
                    refine ⟨1460141804815686650922457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1946855739754248867896609 1460141804815686650922457)
                    ·
                      refine ⟨1095106353611764988191843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1460141804815686650922457 1095106353611764988191843)
                      ·
                        rfl

theorem cell23_2132712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 2, 1, 2, 2].length) (baseStart_2132712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132712 prefixEnd_2132712 := by exact prefixLift 2132712
  have htrace : WordTrace (prefixWord ++ tailWord_2132712) baseStart_2132712 baseEnd_2132712 := by
    simpa [prefixWord, tailWord_2132712, baseEnd_2132712] using wordTrace_append hprefix tailTrace_2132712
  have hstable : (prefixWord ++ tailWord_2132712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132712).length < 2 ^ (prefixWord ++ tailWord_2132712).sum := by decide
  have hdescent : baseEnd_2132712 < baseStart_2132712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132720 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 3]
def baseStart_2132720 : Nat := 118140960795 + 2132720 * 2 ^ 59
def prefixEnd_2132720 : Nat := 4983230072969 + 3 ^ 40 * 2132720 * 2
def baseEnd_2132720 : Nat := 1095110461457000956891805

theorem tailTrace_2132720 : CollatzResearch.WordTrace tailWord_2132720 prefixEnd_2132720 1095110461457000956891805 := by
  unfold tailWord_2132720
  simp only [CollatzResearch.WordTrace]
  refine ⟨38893344416763577211257807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51857792555684769615010409 38893344416763577211257807)
  ·
    refine ⟨58340016625145365816886711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38893344416763577211257807 58340016625145365816886711)
    ·
      refine ⟨87510024937718048725330067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58340016625145365816886711 87510024937718048725330067)
      ·
        refine ⟨131265037406577073087995101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87510024937718048725330067 131265037406577073087995101)
        ·
          refine ⟨49224389027466402407998163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131265037406577073087995101 49224389027466402407998163)
          ·
            refine ⟨73836583541199603611997245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49224389027466402407998163 73836583541199603611997245)
            ·
              refine ⟨27688718827949851354498967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73836583541199603611997245 27688718827949851354498967)
              ·
                refine ⟨41533078241924777031748451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27688718827949851354498967 41533078241924777031748451)
                ·
                  refine ⟨62299617362887165547622677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41533078241924777031748451 62299617362887165547622677)
                  ·
                    refine ⟨2920294563885335885044813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 62299617362887165547622677 2920294563885335885044813)
                    ·
                      refine ⟨1095110461457000956891805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2920294563885335885044813 1095110461457000956891805)
                      ·
                        rfl

theorem cell23_2132720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 3].length) (baseStart_2132720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132720 prefixEnd_2132720 := by exact prefixLift 2132720
  have htrace : WordTrace (prefixWord ++ tailWord_2132720) baseStart_2132720 baseEnd_2132720 := by
    simpa [prefixWord, tailWord_2132720, baseEnd_2132720] using wordTrace_append hprefix tailTrace_2132720
  have hstable : (prefixWord ++ tailWord_2132720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132720).length < 2 ^ (prefixWord ++ tailWord_2132720).sum := by decide
  have hdescent : baseEnd_2132720 < baseStart_2132720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132730 : List Nat := [3, 1, 1, 1, 1, 3, 3, 1, 1, 4, 4]
def baseStart_2132730 : Nat := 118140960795 + 2132730 * 2 ^ 59
def prefixEnd_2132730 : Nat := 4983230072969 + 3 ^ 40 * 2132730 * 2
def baseEnd_2132730 : Nat := 1095115596263545917766759

theorem tailTrace_2132730 : CollatzResearch.WordTrace tailWord_2132730 prefixEnd_2132730 1095115596263545917766759 := by
  unfold tailWord_2132730
  simp only [CollatzResearch.WordTrace]
  refine ⟨19446763390872731532594911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51858035708993950753586429 19446763390872731532594911)
  ·
    refine ⟨29170145086309097298892367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19446763390872731532594911 29170145086309097298892367)
    ·
      refine ⟨43755217629463645948338551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29170145086309097298892367 43755217629463645948338551)
      ·
        refine ⟨65632826444195468922507827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43755217629463645948338551 65632826444195468922507827)
        ·
          refine ⟨98449239666293203383761741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65632826444195468922507827 98449239666293203383761741)
          ·
            refine ⟨36918464874859951268910653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98449239666293203383761741 36918464874859951268910653)
            ·
              refine ⟨13844424328072481725841495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36918464874859951268910653 13844424328072481725841495)
              ·
                refine ⟨20766636492108722588762243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13844424328072481725841495 20766636492108722588762243)
                ·
                  refine ⟨31149954738163083883143365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20766636492108722588762243 31149954738163083883143365)
                  ·
                    refine ⟨5840616513405578228089381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31149954738163083883143365 5840616513405578228089381)
                    ·
                      refine ⟨1095115596263545917766759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5840616513405578228089381 1095115596263545917766759)
                      ·
                        rfl

theorem cell23_2132730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 1, 4, 4].length) (baseStart_2132730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132730 prefixEnd_2132730 := by exact prefixLift 2132730
  have htrace : WordTrace (prefixWord ++ tailWord_2132730) baseStart_2132730 baseEnd_2132730 := by
    simpa [prefixWord, tailWord_2132730, baseEnd_2132730] using wordTrace_append hprefix tailTrace_2132730
  have hstable : (prefixWord ++ tailWord_2132730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132730).length < 2 ^ (prefixWord ++ tailWord_2132730).sum := by decide
  have hdescent : baseEnd_2132730 < baseStart_2132730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132750 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 1, 2, 7]
def baseStart_2132750 : Nat := 118140960795 + 2132750 * 2 ^ 59
def prefixEnd_2132750 : Nat := 4983230072969 + 3 ^ 40 * 2132750 * 2
def baseEnd_2132750 : Nat := 1095125865876635839516667

theorem tailTrace_2132750 : CollatzResearch.WordTrace tailWord_2132750 prefixEnd_2132750 1095125865876635839516667 := by
  unfold tailWord_2132750
  simp only [CollatzResearch.WordTrace]
  refine ⟨9723472877927308693263463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51858522015612313030738469 9723472877927308693263463)
  ·
    refine ⟨14585209316890963039895195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9723472877927308693263463 14585209316890963039895195)
    ·
      refine ⟨21877813975336444559842793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14585209316890963039895195 21877813975336444559842793)
      ·
        refine ⟨16408360481502333419882095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21877813975336444559842793 16408360481502333419882095)
        ·
          refine ⟨24612540722253500129823143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16408360481502333419882095 24612540722253500129823143)
          ·
            refine ⟨36918811083380250194734715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24612540722253500129823143 36918811083380250194734715)
            ·
              refine ⟨55378216625070375292102073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36918811083380250194734715 55378216625070375292102073)
              ·
                refine ⟨41533662468802781469076555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55378216625070375292102073 41533662468802781469076555)
                ·
                  refine ⟨62300493703204172203614833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41533662468802781469076555 62300493703204172203614833)
                  ·
                    refine ⟨46725370277403129152711125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 62300493703204172203614833 46725370277403129152711125)
                    ·
                      refine ⟨1095125865876635839516667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 46725370277403129152711125 1095125865876635839516667)
                      ·
                        rfl

theorem cell23_2132750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_2132750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132750 prefixEnd_2132750 := by exact prefixLift 2132750
  have htrace : WordTrace (prefixWord ++ tailWord_2132750) baseStart_2132750 baseEnd_2132750 := by
    simpa [prefixWord, tailWord_2132750, baseEnd_2132750] using wordTrace_append hprefix tailTrace_2132750
  have hstable : (prefixWord ++ tailWord_2132750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132750).length < 2 ^ (prefixWord ++ tailWord_2132750).sum := by decide
  have hdescent : baseEnd_2132750 < baseStart_2132750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132767 : List Nat := [1, 1, 2, 4, 2, 2, 1, 2, 2, 3, 3]
def baseStart_2132767 : Nat := 118140960795 + 2132767 * 2 ^ 59
def prefixEnd_2132767 : Nat := 4983230072969 + 3 ^ 40 * 2132767 * 2
def baseEnd_2132767 : Nat := 1095134595047762273004089

theorem tailTrace_2132767 : CollatzResearch.WordTrace tailWord_2132767 prefixEnd_2132767 1095134595047762273004089 := by
  unfold tailWord_2132767
  simp only [CollatzResearch.WordTrace]
  refine ⟨77788403064356881449476555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51858935376237920966317703 77788403064356881449476555)
  ·
    refine ⟨116682604596535322174214833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77788403064356881449476555 116682604596535322174214833)
    ·
      refine ⟨87511953447401491630661125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116682604596535322174214833 87511953447401491630661125)
      ·
        refine ⟨16408491271387779680748961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87511953447401491630661125 16408491271387779680748961)
        ·
          refine ⟨12306368453540834760561721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16408491271387779680748961 12306368453540834760561721)
          ·
            refine ⟨9229776340155626070421291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12306368453540834760561721 9229776340155626070421291)
            ·
              refine ⟨13844664510233439105631937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9229776340155626070421291 13844664510233439105631937)
              ·
                refine ⟨10383498382675079329223953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13844664510233439105631937 10383498382675079329223953)
                ·
                  refine ⟨7787623787006309496917965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10383498382675079329223953 7787623787006309496917965)
                  ·
                    refine ⟨2920358920127366061344237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7787623787006309496917965 2920358920127366061344237)
                    ·
                      refine ⟨1095134595047762273004089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2920358920127366061344237 1095134595047762273004089)
                      ·
                        rfl

theorem cell23_2132767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_2132767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132767 prefixEnd_2132767 := by exact prefixLift 2132767
  have htrace : WordTrace (prefixWord ++ tailWord_2132767) baseStart_2132767 baseEnd_2132767 := by
    simpa [prefixWord, tailWord_2132767, baseEnd_2132767] using wordTrace_append hprefix tailTrace_2132767
  have hstable : (prefixWord ++ tailWord_2132767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132767).length < 2 ^ (prefixWord ++ tailWord_2132767).sum := by decide
  have hdescent : baseEnd_2132767 < baseStart_2132767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132768 : List Nat := [2, 1, 1, 5, 1, 4, 1, 2, 2, 2, 2]
def baseStart_2132768 : Nat := 118140960795 + 2132768 * 2 ^ 59
def prefixEnd_2132768 : Nat := 4983230072969 + 3 ^ 40 * 2132768 * 2
def baseEnd_2132768 : Nat := 1095135108528416769091585

theorem tailTrace_2132768 : CollatzResearch.WordTrace tailWord_2132768 prefixEnd_2132768 1095135108528416769091585 := by
  unfold tailWord_2132768
  simp only [CollatzResearch.WordTrace]
  refine ⟨38894219768676629310131479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51858959691568839080175305 38894219768676629310131479)
  ·
    refine ⟨58341329653014943965197219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38894219768676629310131479 58341329653014943965197219)
    ·
      refine ⟨87511994479522415947795829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58341329653014943965197219 87511994479522415947795829)
      ·
        refine ⟨8204249482455226495105859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 87511994479522415947795829 8204249482455226495105859)
        ·
          refine ⟨12306374223682839742658789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8204249482455226495105859 12306374223682839742658789)
          ·
            refine ⟨2307445166940532451748523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12306374223682839742658789 2307445166940532451748523)
            ·
              refine ⟨3461167750410798677622785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2307445166940532451748523 3461167750410798677622785)
              ·
                refine ⟨2595875812808099008217089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3461167750410798677622785 2595875812808099008217089)
                ·
                  refine ⟨1946906859606074256162817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2595875812808099008217089 1946906859606074256162817)
                  ·
                    refine ⟨1460180144704555692122113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1946906859606074256162817 1460180144704555692122113)
                    ·
                      refine ⟨1095135108528416769091585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1460180144704555692122113 1095135108528416769091585)
                      ·
                        rfl

theorem cell23_2132768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_2132768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132768 prefixEnd_2132768 := by exact prefixLift 2132768
  have htrace : WordTrace (prefixWord ++ tailWord_2132768) baseStart_2132768 baseEnd_2132768 := by
    simpa [prefixWord, tailWord_2132768, baseEnd_2132768] using wordTrace_append hprefix tailTrace_2132768
  have hstable : (prefixWord ++ tailWord_2132768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132768).length < 2 ^ (prefixWord ++ tailWord_2132768).sum := by decide
  have hdescent : baseEnd_2132768 < baseStart_2132768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132780 : List Nat := [2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 7]
def baseStart_2132780 : Nat := 118140960795 + 2132780 * 2 ^ 59
def prefixEnd_2132780 : Nat := 4983230072969 + 3 ^ 40 * 2132780 * 2
def baseEnd_2132780 : Nat := 1095141270296270722141529

theorem tailTrace_2132780 : CollatzResearch.WordTrace tailWord_2132780 prefixEnd_2132780 1095141270296270722141529 := by
  unfold tailWord_2132780
  simp only [CollatzResearch.WordTrace]
  refine ⟨38894438606654892334849897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51859251475539856446466529 38894438606654892334849897)
  ·
    refine ⟨29170828954991169251137423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38894438606654892334849897 29170828954991169251137423)
    ·
      refine ⟨43756243432486753876706135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29170828954991169251137423 43756243432486753876706135)
      ·
        refine ⟨65634365148730130815059203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43756243432486753876706135 65634365148730130815059203)
        ·
          refine ⟨98451547723095196222588805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65634365148730130815059203 98451547723095196222588805)
          ·
            refine ⟨18459665198080349291735401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98451547723095196222588805 18459665198080349291735401)
            ·
              refine ⟨13844748898560261968801551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18459665198080349291735401 13844748898560261968801551)
              ·
                refine ⟨20767123347840392953202327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13844748898560261968801551 20767123347840392953202327)
                ·
                  refine ⟨31150685021760589429803491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20767123347840392953202327 31150685021760589429803491)
                  ·
                    refine ⟨46726027532640884144705237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31150685021760589429803491 46726027532640884144705237)
                    ·
                      refine ⟨1095141270296270722141529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 46726027532640884144705237 1095141270296270722141529)
                      ·
                        rfl

theorem cell23_2132780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_2132780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132780 prefixEnd_2132780 := by exact prefixLift 2132780
  have htrace : WordTrace (prefixWord ++ tailWord_2132780) baseStart_2132780 baseEnd_2132780 := by
    simpa [prefixWord, tailWord_2132780, baseEnd_2132780] using wordTrace_append hprefix tailTrace_2132780
  have hstable : (prefixWord ++ tailWord_2132780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132780).length < 2 ^ (prefixWord ++ tailWord_2132780).sum := by decide
  have hdescent : baseEnd_2132780 < baseStart_2132780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132807 : List Nat := [1, 1, 4, 1, 2, 1, 1, 5, 2, 1, 4]
def baseStart_2132807 : Nat := 118140960795 + 2132807 * 2 ^ 59
def prefixEnd_2132807 : Nat := 4983230072969 + 3 ^ 40 * 2132807 * 2
def baseEnd_2132807 : Nat := 1095155134273942116503905

theorem tailTrace_2132807 : CollatzResearch.WordTrace tailWord_2132807 prefixEnd_2132807 1095155134273942116503905 := by
  unfold tailWord_2132807
  simp only [CollatzResearch.WordTrace]
  refine ⟨77789861984211968280932675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51859907989474645520621783 77789861984211968280932675)
  ·
    refine ⟨116684792976317952421399013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77789861984211968280932675 116684792976317952421399013)
    ·
      refine ⟨21878398683059616079012315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116684792976317952421399013 21878398683059616079012315)
      ·
        refine ⟨32817598024589424118518473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21878398683059616079012315 32817598024589424118518473)
        ·
          refine ⟨24613198518442068088888855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32817598024589424118518473 24613198518442068088888855)
          ·
            refine ⟨36919797777663102133333283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24613198518442068088888855 36919797777663102133333283)
            ·
              refine ⟨55379696666494653199999925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36919797777663102133333283 55379696666494653199999925)
              ·
                refine ⟨5191846562483873737499993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55379696666494653199999925 5191846562483873737499993)
                ·
                  refine ⟨3893884921862905303124995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5191846562483873737499993 3893884921862905303124995)
                  ·
                    refine ⟨5840827382794357954687493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3893884921862905303124995 5840827382794357954687493)
                    ·
                      refine ⟨1095155134273942116503905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5840827382794357954687493 1095155134273942116503905)
                      ·
                        rfl

theorem cell23_2132807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_2132807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132807 prefixEnd_2132807 := by exact prefixLift 2132807
  have htrace : WordTrace (prefixWord ++ tailWord_2132807) baseStart_2132807 baseEnd_2132807 := by
    simpa [prefixWord, tailWord_2132807, baseEnd_2132807] using wordTrace_append hprefix tailTrace_2132807
  have hstable : (prefixWord ++ tailWord_2132807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132807).length < 2 ^ (prefixWord ++ tailWord_2132807).sum := by decide
  have hdescent : baseEnd_2132807 < baseStart_2132807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132925 : List Nat := [1, 4, 1, 2, 4, 1, 2, 3, 1, 1, 3]
def baseStart_2132925 : Nat := 118140960795 + 2132925 * 2 ^ 59
def prefixEnd_2132925 : Nat := 4983230072969 + 3 ^ 40 * 2132925 * 2
def baseEnd_2132925 : Nat := 1095215724991172654828363

theorem tailTrace_2132925 : CollatzResearch.WordTrace tailWord_2132925 prefixEnd_2132925 1095215724991172654828363 := by
  unfold tailWord_2132925
  simp only [CollatzResearch.WordTrace]
  refine ⟨77794165797784474433728229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51862777198522982955818819 77794165797784474433728229)
  ·
    refine ⟨14586406087084588956324043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77794165797784474433728229 14586406087084588956324043)
    ·
      refine ⟨21879609130626883434486065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14586406087084588956324043 21879609130626883434486065)
      ·
        refine ⟨16409706847970162575864549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21879609130626883434486065 16409706847970162575864549)
        ·
          refine ⟨3076820033994405482974603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16409706847970162575864549 3076820033994405482974603)
          ·
            refine ⟨4615230050991608224461905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3076820033994405482974603 4615230050991608224461905)
            ·
              refine ⟨3461422538243706168346429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4615230050991608224461905 3461422538243706168346429)
              ·
                refine ⟨1298033451841389813129911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3461422538243706168346429 1298033451841389813129911)
                ·
                  refine ⟨1947050177762084719694867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1298033451841389813129911 1947050177762084719694867)
                  ·
                    refine ⟨2920575266643127079542301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1947050177762084719694867 2920575266643127079542301)
                    ·
                      refine ⟨1095215724991172654828363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2920575266643127079542301 1095215724991172654828363)
                      ·
                        rfl

theorem cell23_2132925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 3, 1, 1, 3].length) (baseStart_2132925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132925 prefixEnd_2132925 := by exact prefixLift 2132925
  have htrace : WordTrace (prefixWord ++ tailWord_2132925) baseStart_2132925 baseEnd_2132925 := by
    simpa [prefixWord, tailWord_2132925, baseEnd_2132925] using wordTrace_append hprefix tailTrace_2132925
  have hstable : (prefixWord ++ tailWord_2132925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132925).length < 2 ^ (prefixWord ++ tailWord_2132925).sum := by decide
  have hdescent : baseEnd_2132925 < baseStart_2132925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132927 : List Nat := [1, 1, 2, 2, 2, 1, 2, 3, 3, 2, 4]
def baseStart_2132927 : Nat := 118140960795 + 2132927 * 2 ^ 59
def prefixEnd_2132927 : Nat := 4983230072969 + 3 ^ 40 * 2132927 * 2
def baseEnd_2132927 : Nat := 1095216751952481647003353

theorem tailTrace_2132927 : CollatzResearch.WordTrace tailWord_2132927 prefixEnd_2132927 1095216751952481647003353 := by
  unfold tailWord_2132927
  simp only [CollatzResearch.WordTrace]
  refine ⟨77794238743777228775301035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51862825829184819183534023 77794238743777228775301035)
  ·
    refine ⟨116691358115665843162951553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77794238743777228775301035 116691358115665843162951553)
    ·
      refine ⟨87518518586749382372213665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116691358115665843162951553 87518518586749382372213665)
      ·
        refine ⟨65638888940062036779160249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87518518586749382372213665 65638888940062036779160249)
        ·
          refine ⟨49229166705046527584370187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65638888940062036779160249 49229166705046527584370187)
          ·
            refine ⟨73843750057569791376555281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49229166705046527584370187 73843750057569791376555281)
            ·
              refine ⟨55382812543177343532416461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73843750057569791376555281 55382812543177343532416461)
              ·
                refine ⟨20768554703691503824656173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55382812543177343532416461 20768554703691503824656173)
                ·
                  refine ⟨7788208013884313934246065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20768554703691503824656173 7788208013884313934246065)
                  ·
                    refine ⟨5841156010413235450684549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7788208013884313934246065 5841156010413235450684549)
                    ·
                      refine ⟨1095216751952481647003353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5841156010413235450684549 1095216751952481647003353)
                      ·
                        rfl

theorem cell23_2132927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2, 4].length) (baseStart_2132927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132927 prefixEnd_2132927 := by exact prefixLift 2132927
  have htrace : WordTrace (prefixWord ++ tailWord_2132927) baseStart_2132927 baseEnd_2132927 := by
    simpa [prefixWord, tailWord_2132927, baseEnd_2132927] using wordTrace_append hprefix tailTrace_2132927
  have hstable : (prefixWord ++ tailWord_2132927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132927).length < 2 ^ (prefixWord ++ tailWord_2132927).sum := by decide
  have hdescent : baseEnd_2132927 < baseStart_2132927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132948 : List Nat := [2, 4, 1, 2, 1, 2, 1, 3, 3, 2, 2]
def baseStart_2132948 : Nat := 118140960795 + 2132948 * 2 ^ 59
def prefixEnd_2132948 : Nat := 4983230072969 + 3 ^ 40 * 2132948 * 2
def baseEnd_2132948 : Nat := 1095227535046226064840757

theorem tailTrace_2132948 : CollatzResearch.WordTrace tailWord_2132948 prefixEnd_2132948 1095227535046226064840757 := by
  unfold tailWord_2132948
  simp only [CollatzResearch.WordTrace]
  refine ⟨38897502338350574680907749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51863336451134099574543665 38897502338350574680907749)
  ·
    refine ⟨7293281688440732752670203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38897502338350574680907749 7293281688440732752670203)
    ·
      refine ⟨10939922532661099129005305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7293281688440732752670203 10939922532661099129005305)
      ·
        refine ⟨8204941899495824346753979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10939922532661099129005305 8204941899495824346753979)
        ·
          refine ⟨12307412849243736520130969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8204941899495824346753979 12307412849243736520130969)
          ·
            refine ⟨9230559636932802390098227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12307412849243736520130969 9230559636932802390098227)
            ·
              refine ⟨13845839455399203585147341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9230559636932802390098227 13845839455399203585147341)
              ·
                refine ⟨5192189795774701344430253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13845839455399203585147341 5192189795774701344430253)
                ·
                  refine ⟨1947071173415513004161345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5192189795774701344430253 1947071173415513004161345)
                  ·
                    refine ⟨1460303380061634753121009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1947071173415513004161345 1460303380061634753121009)
                    ·
                      refine ⟨1095227535046226064840757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1460303380061634753121009 1095227535046226064840757)
                      ·
                        rfl

theorem cell23_2132948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_2132948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132948 prefixEnd_2132948 := by exact prefixLift 2132948
  have htrace : WordTrace (prefixWord ++ tailWord_2132948) baseStart_2132948 baseEnd_2132948 := by
    simpa [prefixWord, tailWord_2132948, baseEnd_2132948] using wordTrace_append hprefix tailTrace_2132948
  have hstable : (prefixWord ++ tailWord_2132948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132948).length < 2 ^ (prefixWord ++ tailWord_2132948).sum := by decide
  have hdescent : baseEnd_2132948 < baseStart_2132948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132964 : List Nat := [2, 3, 1, 1, 1, 1, 2, 5, 1, 3, 3]
def baseStart_2132964 : Nat := 118140960795 + 2132964 * 2 ^ 59
def prefixEnd_2132964 : Nat := 4983230072969 + 3 ^ 40 * 2132964 * 2
def baseEnd_2132964 : Nat := 1095235750736698002240683

theorem tailTrace_2132964 : CollatzResearch.WordTrace tailWord_2132964 prefixEnd_2132964 1095235750736698002240683 := by
  unfold tailWord_2132964
  simp only [CollatzResearch.WordTrace]
  refine ⟨38897794122321592047198973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51863725496428789396265297 38897794122321592047198973)
  ·
    refine ⟨14586672795870597017699615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38897794122321592047198973 14586672795870597017699615)
    ·
      refine ⟨21880009193805895526549423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14586672795870597017699615 21880009193805895526549423)
      ·
        refine ⟨32820013790708843289824135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21880009193805895526549423 32820013790708843289824135)
        ·
          refine ⟨49230020686063264934736203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32820013790708843289824135 49230020686063264934736203)
          ·
            refine ⟨73845031029094897402104305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49230020686063264934736203 73845031029094897402104305)
            ·
              refine ⟨55383773271821173051578229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73845031029094897402104305 55383773271821173051578229)
              ·
                refine ⟨5192228744233234973585459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55383773271821173051578229 5192228744233234973585459)
                ·
                  refine ⟨7788343116349852460378189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5192228744233234973585459 7788343116349852460378189)
                  ·
                    refine ⟨2920628668631194672641821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7788343116349852460378189 2920628668631194672641821)
                    ·
                      refine ⟨1095235750736698002240683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2920628668631194672641821 1095235750736698002240683)
                      ·
                        rfl

theorem cell23_2132964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 1, 3, 3].length) (baseStart_2132964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132964 prefixEnd_2132964 := by exact prefixLift 2132964
  have htrace : WordTrace (prefixWord ++ tailWord_2132964) baseStart_2132964 baseEnd_2132964 := by
    simpa [prefixWord, tailWord_2132964, baseEnd_2132964] using wordTrace_append hprefix tailTrace_2132964
  have hstable : (prefixWord ++ tailWord_2132964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132964).length < 2 ^ (prefixWord ++ tailWord_2132964).sum := by decide
  have hdescent : baseEnd_2132964 < baseStart_2132964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132982 : List Nat := [5, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2]
def baseStart_2132982 : Nat := 118140960795 + 2132982 * 2 ^ 59
def prefixEnd_2132982 : Nat := 4983230072969 + 3 ^ 40 * 2132982 * 2
def baseEnd_2132982 : Nat := 1095244993388478931815601

theorem tailTrace_2132982 : CollatzResearch.WordTrace tailWord_2132982 prefixEnd_2132982 1095244993388478931815601 := by
  unfold tailWord_2132982
  simp only [CollatzResearch.WordTrace]
  refine ⟨4862265297411123323034575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51864163172385315445702133 4862265297411123323034575)
  ·
    refine ⟨7293397946116684984551863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4862265297411123323034575 7293397946116684984551863)
    ·
      refine ⟨10940096919175027476827795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7293397946116684984551863 10940096919175027476827795)
      ·
        refine ⟨16410145378762541215241693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10940096919175027476827795 16410145378762541215241693)
        ·
          refine ⟨6153804517035952955715635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16410145378762541215241693 6153804517035952955715635)
          ·
            refine ⟨9230706775553929433573453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6153804517035952955715635 9230706775553929433573453)
            ·
              refine ⟨3461515040832723537590045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9230706775553929433573453 3461515040832723537590045)
              ·
                refine ⟨1298068140312271326596267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3461515040832723537590045 1298068140312271326596267)
                ·
                  refine ⟨1947102210468406989894401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1298068140312271326596267 1947102210468406989894401)
                  ·
                    refine ⟨1460326657851305242420801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1947102210468406989894401 1460326657851305242420801)
                    ·
                      refine ⟨1095244993388478931815601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1460326657851305242420801 1095244993388478931815601)
                      ·
                        rfl

theorem cell23_2132982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2].length) (baseStart_2132982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132982 prefixEnd_2132982 := by exact prefixLift 2132982
  have htrace : WordTrace (prefixWord ++ tailWord_2132982) baseStart_2132982 baseEnd_2132982 := by
    simpa [prefixWord, tailWord_2132982, baseEnd_2132982] using wordTrace_append hprefix tailTrace_2132982
  have hstable : (prefixWord ++ tailWord_2132982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132982).length < 2 ^ (prefixWord ++ tailWord_2132982).sum := by decide
  have hdescent : baseEnd_2132982 < baseStart_2132982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132987 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 1, 5, 4]
def baseStart_2132987 : Nat := 118140960795 + 2132987 * 2 ^ 59
def prefixEnd_2132987 : Nat := 4983230072969 + 3 ^ 40 * 2132987 * 2
def baseEnd_2132987 : Nat := 1095247560791751412253077

theorem tailTrace_2132987 : CollatzResearch.WordTrace tailWord_2132987 prefixEnd_2132987 1095247560791751412253077 := by
  unfold tailWord_2132987
  simp only [CollatzResearch.WordTrace]
  refine ⟨77796427123559859022485215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51864284749039906014990143 77796427123559859022485215)
  ·
    refine ⟨116694640685339788533727823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77796427123559859022485215 116694640685339788533727823)
    ·
      refine ⟨175041961028009682800591735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116694640685339788533727823 175041961028009682800591735)
      ·
        refine ⟨262562941542014524200887603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175041961028009682800591735 262562941542014524200887603)
        ·
          refine ⟨393844412313021786301331405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262562941542014524200887603 393844412313021786301331405)
          ·
            refine ⟨147691654617383169862999277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 393844412313021786301331405 147691654617383169862999277)
            ·
              refine ⟨55384370481518688698624729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 147691654617383169862999277 55384370481518688698624729)
              ·
                refine ⟨41538277861139016523968547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55384370481518688698624729 41538277861139016523968547)
                ·
                  refine ⟨62307416791708524785952821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41538277861139016523968547 62307416791708524785952821)
                  ·
                    refine ⟨5841320324222674198683077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 62307416791708524785952821 5841320324222674198683077)
                    ·
                      refine ⟨1095247560791751412253077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5841320324222674198683077 1095247560791751412253077)
                      ·
                        rfl

theorem cell23_2132987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 5, 4].length) (baseStart_2132987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132987 prefixEnd_2132987 := by exact prefixLift 2132987
  have htrace : WordTrace (prefixWord ++ tailWord_2132987) baseStart_2132987 baseEnd_2132987 := by
    simpa [prefixWord, tailWord_2132987, baseEnd_2132987] using wordTrace_append hprefix tailTrace_2132987
  have hstable : (prefixWord ++ tailWord_2132987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132987).length < 2 ^ (prefixWord ++ tailWord_2132987).sum := by decide
  have hdescent : baseEnd_2132987 < baseStart_2132987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133015 : List Nat := [1, 1, 3, 5, 1, 1, 4, 1, 2, 1, 3]
def baseStart_2133015 : Nat := 118140960795 + 2133015 * 2 ^ 59
def prefixEnd_2133015 : Nat := 4983230072969 + 3 ^ 40 * 2133015 * 2
def baseEnd_2133015 : Nat := 1095261938250077302702949

theorem tailTrace_2133015 : CollatzResearch.WordTrace tailWord_2133015 prefixEnd_2133015 1095261938250077302702949 := by
  unfold tailWord_2133015
  simp only [CollatzResearch.WordTrace]
  refine ⟨77797448367458419804504499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51864965578305613203002999 77797448367458419804504499)
  ·
    refine ⟨116696172551187629706756749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77797448367458419804504499 116696172551187629706756749)
    ·
      refine ⟨43761064706695361140033781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116696172551187629706756749 43761064706695361140033781)
      ·
        refine ⟨4102599816252690106878167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43761064706695361140033781 4102599816252690106878167)
        ·
          refine ⟨6153899724379035160317251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4102599816252690106878167 6153899724379035160317251)
          ·
            refine ⟨9230849586568552740475877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6153899724379035160317251 9230849586568552740475877)
            ·
              refine ⟨1730784297481603638839227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9230849586568552740475877 1730784297481603638839227)
              ·
                refine ⟨2596176446222405458258841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1730784297481603638839227 2596176446222405458258841)
                ·
                  refine ⟨1947132334666804093694131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2596176446222405458258841 1947132334666804093694131)
                  ·
                    refine ⟨2920698502000206140541197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1947132334666804093694131 2920698502000206140541197)
                    ·
                      refine ⟨1095261938250077302702949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2920698502000206140541197 1095261938250077302702949)
                      ·
                        rfl

theorem cell23_2133015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_2133015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133015 prefixEnd_2133015 := by exact prefixLift 2133015
  have htrace : WordTrace (prefixWord ++ tailWord_2133015) baseStart_2133015 baseEnd_2133015 := by
    simpa [prefixWord, tailWord_2133015, baseEnd_2133015] using wordTrace_append hprefix tailTrace_2133015
  have hstable : (prefixWord ++ tailWord_2133015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133015).length < 2 ^ (prefixWord ++ tailWord_2133015).sum := by decide
  have hdescent : baseEnd_2133015 < baseStart_2133015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133025 : List Nat := [1, 2, 3, 2, 3, 3, 1, 2, 1, 3, 2]
def baseStart_2133025 : Nat := 118140960795 + 2133025 * 2 ^ 59
def prefixEnd_2133025 : Nat := 4983230072969 + 3 ^ 40 * 2133025 * 2
def baseEnd_2133025 : Nat := 1095267073056622263577903

theorem tailTrace_2133025 : CollatzResearch.WordTrace tailWord_2133025 prefixEnd_2133025 1095267073056622263577903 := by
  unfold tailWord_2133025
  simp only [CollatzResearch.WordTrace]
  refine ⟨77797813097422191512368529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51865208731614794341579019 77797813097422191512368529)
  ·
    refine ⟨58348359823066643634276397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77797813097422191512368529 58348359823066643634276397)
    ·
      refine ⟨21880634933649991362853649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58348359823066643634276397 21880634933649991362853649)
      ·
        refine ⟨16410476200237493522140237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21880634933649991362853649 16410476200237493522140237)
        ·
          refine ⟨6153928575089060070802589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16410476200237493522140237 6153928575089060070802589)
          ·
            refine ⟨2307723215658397526550971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6153928575089060070802589 2307723215658397526550971)
            ·
              refine ⟨3461584823487596289826457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2307723215658397526550971 3461584823487596289826457)
              ·
                refine ⟨2596188617615697217369843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3461584823487596289826457 2596188617615697217369843)
                ·
                  refine ⟨3894282926423545826054765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2596188617615697217369843 3894282926423545826054765)
                  ·
                    refine ⟨1460356097408829684770537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3894282926423545826054765 1460356097408829684770537)
                    ·
                      refine ⟨1095267073056622263577903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1460356097408829684770537 1095267073056622263577903)
                      ·
                        rfl

theorem cell23_2133025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 2, 1, 3, 2].length) (baseStart_2133025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133025 prefixEnd_2133025 := by exact prefixLift 2133025
  have htrace : WordTrace (prefixWord ++ tailWord_2133025) baseStart_2133025 baseEnd_2133025 := by
    simpa [prefixWord, tailWord_2133025, baseEnd_2133025] using wordTrace_append hprefix tailTrace_2133025
  have hstable : (prefixWord ++ tailWord_2133025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133025).length < 2 ^ (prefixWord ++ tailWord_2133025).sum := by decide
  have hdescent : baseEnd_2133025 < baseStart_2133025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133038 : List Nat := [4, 1, 3, 1, 1, 1, 3, 2, 1, 4, 2]
def baseStart_2133038 : Nat := 118140960795 + 2133038 * 2 ^ 59
def prefixEnd_2133038 : Nat := 4983230072969 + 3 ^ 40 * 2133038 * 2
def baseEnd_2133038 : Nat := 1095273748305130712715343

theorem tailTrace_2133038 : CollatzResearch.WordTrace tailWord_2133038 prefixEnd_2133038 1095273748305130712715343 := by
  unfold tailWord_2133038
  simp only [CollatzResearch.WordTrace]
  refine ⟨9724785905796886841573971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51865524830916729821727845 9724785905796886841573971)
  ·
    refine ⟨14587178858695330262360957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9724785905796886841573971 14587178858695330262360957)
    ·
      refine ⟨5470192072010748848385359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14587178858695330262360957 5470192072010748848385359)
      ·
        refine ⟨8205288108016123272578039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5470192072010748848385359 8205288108016123272578039)
        ·
          refine ⟨12307932162024184908867059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8205288108016123272578039 12307932162024184908867059)
          ·
            refine ⟨18461898243036277363300589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12307932162024184908867059 18461898243036277363300589)
            ·
              refine ⟨6923211841138604011237721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18461898243036277363300589 6923211841138604011237721)
              ·
                refine ⟨5192408880853953008428291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6923211841138604011237721 5192408880853953008428291)
                ·
                  refine ⟨7788613321280929512642437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5192408880853953008428291 7788613321280929512642437)
                  ·
                    refine ⟨1460364997740174283620457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7788613321280929512642437 1460364997740174283620457)
                    ·
                      refine ⟨1095273748305130712715343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1460364997740174283620457 1095273748305130712715343)
                      ·
                        rfl

theorem cell23_2133038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_2133038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133038 prefixEnd_2133038 := by exact prefixLift 2133038
  have htrace : WordTrace (prefixWord ++ tailWord_2133038) baseStart_2133038 baseEnd_2133038 := by
    simpa [prefixWord, tailWord_2133038, baseEnd_2133038] using wordTrace_append hprefix tailTrace_2133038
  have hstable : (prefixWord ++ tailWord_2133038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133038).length < 2 ^ (prefixWord ++ tailWord_2133038).sum := by decide
  have hdescent : baseEnd_2133038 < baseStart_2133038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133111 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 4, 4, 2]
def baseStart_2133111 : Nat := 118140960795 + 2133111 * 2 ^ 59
def prefixEnd_2133111 : Nat := 4983230072969 + 3 ^ 40 * 2133111 * 2
def baseEnd_2133111 : Nat := 1095311232392908927102507

theorem tailTrace_2133111 : CollatzResearch.WordTrace tailWord_2133111 prefixEnd_2133111 1095311232392908927102507 := by
  unfold tailWord_2133111
  simp only [CollatzResearch.WordTrace]
  refine ⟨77800949775110628199999187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51867299850073752133332791 77800949775110628199999187)
  ·
    refine ⟨116701424662665942299998781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77800949775110628199999187 116701424662665942299998781)
    ·
      refine ⟨43763034248499728362499543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116701424662665942299998781 43763034248499728362499543)
      ·
        refine ⟨65644551372749592543749315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43763034248499728362499543 65644551372749592543749315)
        ·
          refine ⟨98466827059124388815623973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65644551372749592543749315 98466827059124388815623973)
          ·
            refine ⟨18462530073585822902929495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98466827059124388815623973 18462530073585822902929495)
            ·
              refine ⟨27693795110378734354394243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18462530073585822902929495 27693795110378734354394243)
              ·
                refine ⟨41540692665568101531591365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27693795110378734354394243 41540692665568101531591365)
                ·
                  refine ⟨7788879874794019037173381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41540692665568101531591365 7788879874794019037173381)
                  ·
                    refine ⟨1460414976523878569470009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7788879874794019037173381 1460414976523878569470009)
                    ·
                      refine ⟨1095311232392908927102507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1460414976523878569470009 1095311232392908927102507)
                      ·
                        rfl

theorem cell23_2133111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 4, 2].length) (baseStart_2133111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133111 prefixEnd_2133111 := by exact prefixLift 2133111
  have htrace : WordTrace (prefixWord ++ tailWord_2133111) baseStart_2133111 baseEnd_2133111 := by
    simpa [prefixWord, tailWord_2133111, baseEnd_2133111] using wordTrace_append hprefix tailTrace_2133111
  have hstable : (prefixWord ++ tailWord_2133111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133111).length < 2 ^ (prefixWord ++ tailWord_2133111).sum := by decide
  have hdescent : baseEnd_2133111 < baseStart_2133111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133138 : List Nat := [3, 2, 3, 1, 1, 2, 2, 2, 3, 4]
def baseStart_2133138 : Nat := 118140960795 + 2133138 * 2 ^ 59
def prefixEnd_2133138 : Nat := 4983230072969 + 3 ^ 40 * 2133138 * 2
def baseEnd_2133138 : Nat := 365108365456860107154961

theorem tailTrace_2133138 : CollatzResearch.WordTrace tailWord_2133138 prefixEnd_2133138 365108365456860107154961 := by
  unfold tailWord_2133138
  simp only [CollatzResearch.WordTrace]
  refine ⟨19450483636503202952808017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51867956364008541207488045 19450483636503202952808017)
  ·
    refine ⟨14587862727377402214606013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19450483636503202952808017 14587862727377402214606013)
    ·
      refine ⟨5470448522766525830477255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14587862727377402214606013 5470448522766525830477255)
      ·
        refine ⟨8205672784149788745715883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5470448522766525830477255 8205672784149788745715883)
        ·
          refine ⟨12308509176224683118573825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8205672784149788745715883 12308509176224683118573825)
          ·
            refine ⟨9231381882168512338930369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12308509176224683118573825 9231381882168512338930369)
            ·
              refine ⟨6923536411626384254197777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9231381882168512338930369 6923536411626384254197777)
              ·
                refine ⟨5192652308719788190648333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6923536411626384254197777 5192652308719788190648333)
                ·
                  refine ⟨1947244615769920571493125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5192652308719788190648333 1947244615769920571493125)
                  ·
                    refine ⟨365108365456860107154961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1947244615769920571493125 365108365456860107154961)
                    ·
                      rfl

theorem cell23_2133138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_2133138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133138 prefixEnd_2133138 := by exact prefixLift 2133138
  have htrace : WordTrace (prefixWord ++ tailWord_2133138) baseStart_2133138 baseEnd_2133138 := by
    simpa [prefixWord, tailWord_2133138, baseEnd_2133138] using wordTrace_append hprefix tailTrace_2133138
  have hstable : (prefixWord ++ tailWord_2133138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133138).length < 2 ^ (prefixWord ++ tailWord_2133138).sum := by decide
  have hdescent : baseEnd_2133138 < baseStart_2133138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133165 : List Nat := [1, 5, 2, 1, 3, 1, 1, 2, 2, 2, 3]
def baseStart_2133165 : Nat := 118140960795 + 2133165 * 2 ^ 59
def prefixEnd_2133165 : Nat := 4983230072969 + 3 ^ 40 * 2133165 * 2
def baseEnd_2133165 : Nat := 1095338960348251715827259

theorem tailTrace_2133165 : CollatzResearch.WordTrace tailWord_2133165 prefixEnd_2133165 1095338960348251715827259 := by
  unfold tailWord_2133165
  simp only [CollatzResearch.WordTrace]
  refine ⟨77802919316914995422464949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51868612877943330281643299 77802919316914995422464949)
  ·
    refine ⟨7294023685960780820856089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77802919316914995422464949 7294023685960780820856089)
    ·
      refine ⟨5470517764470585615642067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7294023685960780820856089 5470517764470585615642067)
      ·
        refine ⟨8205776646705878423463101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5470517764470585615642067 8205776646705878423463101)
        ·
          refine ⟨3077166242514704408798663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8205776646705878423463101 3077166242514704408798663)
          ·
            refine ⟨4615749363772056613197995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3077166242514704408798663 4615749363772056613197995)
            ·
              refine ⟨6923624045658084919796993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4615749363772056613197995 6923624045658084919796993)
              ·
                refine ⟨5192718034243563689847745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6923624045658084919796993 5192718034243563689847745)
                ·
                  refine ⟨3894538525682672767385809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5192718034243563689847745 3894538525682672767385809)
                  ·
                    refine ⟨2920903894262004575539357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3894538525682672767385809 2920903894262004575539357)
                    ·
                      refine ⟨1095338960348251715827259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2920903894262004575539357 1095338960348251715827259)
                      ·
                        rfl

theorem cell23_2133165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_2133165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133165 prefixEnd_2133165 := by exact prefixLift 2133165
  have htrace : WordTrace (prefixWord ++ tailWord_2133165) baseStart_2133165 baseEnd_2133165 := by
    simpa [prefixWord, tailWord_2133165, baseEnd_2133165] using wordTrace_append hprefix tailTrace_2133165
  have hstable : (prefixWord ++ tailWord_2133165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133165).length < 2 ^ (prefixWord ++ tailWord_2133165).sum := by decide
  have hdescent : baseEnd_2133165 < baseStart_2133165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133185 : List Nat := [1, 2, 6, 1, 1, 1, 4, 1, 6]
def baseStart_2133185 : Nat := 118140960795 + 2133185 * 2 ^ 59
def prefixEnd_2133185 : Nat := 4983230072969 + 3 ^ 40 * 2133185 * 2
def baseEnd_2133185 : Nat := 121705469995704626397463

theorem tailTrace_2133185 : CollatzResearch.WordTrace tailWord_2133185 prefixEnd_2133185 121705469995704626397463 := by
  unfold tailWord_2133185
  simp only [CollatzResearch.WordTrace]
  refine ⟨77803648776842538838193009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51869099184561692558795339 77803648776842538838193009)
  ·
    refine ⟨58352736582631904128644757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77803648776842538838193009 58352736582631904128644757)
    ·
      refine ⟨2735284527310870506030223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 58352736582631904128644757 2735284527310870506030223)
      ·
        refine ⟨4102926790966305759045335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2735284527310870506030223 4102926790966305759045335)
        ·
          refine ⟨6154390186449458638568003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4102926790966305759045335 6154390186449458638568003)
          ·
            refine ⟨9231585279674187957852005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6154390186449458638568003 9231585279674187957852005)
            ·
              refine ⟨1730922239938910242097251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9231585279674187957852005 1730922239938910242097251)
              ·
                refine ⟨2596383359908365363145877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1730922239938910242097251 2596383359908365363145877)
                ·
                  refine ⟨121705469995704626397463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2596383359908365363145877 121705469995704626397463)
                  ·
                    rfl

theorem cell23_2133185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 1, 6].length) (baseStart_2133185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133185 prefixEnd_2133185 := by exact prefixLift 2133185
  have htrace : WordTrace (prefixWord ++ tailWord_2133185) baseStart_2133185 baseEnd_2133185 := by
    simpa [prefixWord, tailWord_2133185, baseEnd_2133185] using wordTrace_append hprefix tailTrace_2133185
  have hstable : (prefixWord ++ tailWord_2133185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133185).length < 2 ^ (prefixWord ++ tailWord_2133185).sum := by decide
  have hdescent : baseEnd_2133185 < baseStart_2133185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133198 : List Nat := [4, 1, 1, 1, 5, 1, 1, 1, 3, 5]
def baseStart_2133198 : Nat := 118140960795 + 2133198 * 2 ^ 59
def prefixEnd_2133198 : Nat := 4983230072969 + 3 ^ 40 * 2133198 * 2
def baseEnd_2133198 : Nat := 365118635069950028904869

theorem tailTrace_2133198 : CollatzResearch.WordTrace tailWord_2133198 prefixEnd_2133198 365118635069950028904869 := by
  unfold tailWord_2133198
  simp only [CollatzResearch.WordTrace]
  refine ⟨9725515365724430257302031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51869415283863628038944165 9725515365724430257302031)
  ·
    refine ⟨14588273048586645385953047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9725515365724430257302031 14588273048586645385953047)
    ·
      refine ⟨21882409572879968078929571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14588273048586645385953047 21882409572879968078929571)
      ·
        refine ⟨32823614359319952118394357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21882409572879968078929571 32823614359319952118394357)
        ·
          refine ⟨3077213846186245511099471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32823614359319952118394357 3077213846186245511099471)
          ·
            refine ⟨4615820769279368266649207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3077213846186245511099471 4615820769279368266649207)
            ·
              refine ⟨6923731153919052399973811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4615820769279368266649207 6923731153919052399973811)
              ·
                refine ⟨10385596730878578599960717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6923731153919052399973811 10385596730878578599960717)
                ·
                  refine ⟨3894598774079466974985269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10385596730878578599960717 3894598774079466974985269)
                  ·
                    refine ⟨365118635069950028904869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3894598774079466974985269 365118635069950028904869)
                    ·
                      rfl

theorem cell23_2133198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 3, 5].length) (baseStart_2133198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133198 prefixEnd_2133198 := by exact prefixLift 2133198
  have htrace : WordTrace (prefixWord ++ tailWord_2133198) baseStart_2133198 baseEnd_2133198 := by
    simpa [prefixWord, tailWord_2133198, baseEnd_2133198] using wordTrace_append hprefix tailTrace_2133198
  have hstable : (prefixWord ++ tailWord_2133198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133198).length < 2 ^ (prefixWord ++ tailWord_2133198).sum := by decide
  have hdescent : baseEnd_2133198 < baseStart_2133198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133205 : List Nat := [1, 3, 2, 4, 1, 1, 1, 3, 2, 3, 2]
def baseStart_2133205 : Nat := 118140960795 + 2133205 * 2 ^ 59
def prefixEnd_2133205 : Nat := 4983230072969 + 3 ^ 40 * 2133205 * 2
def baseEnd_2133205 : Nat := 1095359499574431559327075

theorem tailTrace_2133205 : CollatzResearch.WordTrace tailWord_2133205 prefixEnd_2133205 1095359499574431559327075 := by
  unfold tailWord_2133205
  simp only [CollatzResearch.WordTrace]
  refine ⟨77804378236770082253921069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51869585491180054835947379 77804378236770082253921069)
  ·
    refine ⟨29176641838788780845220401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77804378236770082253921069 29176641838788780845220401)
    ·
      refine ⟨21882481379091585633915301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29176641838788780845220401 21882481379091585633915301)
      ·
        refine ⟨4102965258579672306359119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21882481379091585633915301 4102965258579672306359119)
        ·
          refine ⟨6154447887869508459538679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4102965258579672306359119 6154447887869508459538679)
          ·
            refine ⟨9231671831804262689308019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6154447887869508459538679 9231671831804262689308019)
            ·
              refine ⟨13847507747706394033962029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9231671831804262689308019 13847507747706394033962029)
              ·
                refine ⟨5192815405389897762735761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13847507747706394033962029 5192815405389897762735761)
                ·
                  refine ⟨3894611554042423322051821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5192815405389897762735761 3894611554042423322051821)
                  ·
                    refine ⟨1460479332765908745769433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3894611554042423322051821 1460479332765908745769433)
                    ·
                      refine ⟨1095359499574431559327075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1460479332765908745769433 1095359499574431559327075)
                      ·
                        rfl

theorem cell23_2133205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_2133205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133205 prefixEnd_2133205 := by exact prefixLift 2133205
  have htrace : WordTrace (prefixWord ++ tailWord_2133205) baseStart_2133205 baseEnd_2133205 := by
    simpa [prefixWord, tailWord_2133205, baseEnd_2133205] using wordTrace_append hprefix tailTrace_2133205
  have hstable : (prefixWord ++ tailWord_2133205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133205).length < 2 ^ (prefixWord ++ tailWord_2133205).sum := by decide
  have hdescent : baseEnd_2133205 < baseStart_2133205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133228 : List Nat := [2, 2, 1, 1, 2, 4, 1, 4, 2, 4]
def baseStart_2133228 : Nat := 118140960795 + 2133228 * 2 ^ 59
def prefixEnd_2133228 : Nat := 4983230072969 + 3 ^ 40 * 2133228 * 2
def baseEnd_2133228 : Nat := 365123769876494989779823

theorem tailTrace_2133228 : CollatzResearch.WordTrace tailWord_2133228 prefixEnd_2133228 365123769876494989779823 := by
  unfold tailWord_2133228
  simp only [CollatzResearch.WordTrace]
  refine ⟨38902608557843378591004169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51870144743791171454672225 38902608557843378591004169)
  ·
    refine ⟨29176956418382533943253127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38902608557843378591004169 29176956418382533943253127)
    ·
      refine ⟨43765434627573800914879691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29176956418382533943253127 43765434627573800914879691)
      ·
        refine ⟨65648151941360701372319537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43765434627573800914879691 65648151941360701372319537)
        ·
          refine ⟨49236113956020526029239653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65648151941360701372319537 49236113956020526029239653)
          ·
            refine ⟨9231771366753848630482435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49236113956020526029239653 9231771366753848630482435)
            ·
              refine ⟨13847657050130772945723653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9231771366753848630482435 13847657050130772945723653)
              ·
                refine ⟨2596435696899519927323185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13847657050130772945723653 2596435696899519927323185)
                ·
                  refine ⟨1947326772674639945492389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2596435696899519927323185 1947326772674639945492389)
                  ·
                    refine ⟨365123769876494989779823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1947326772674639945492389 365123769876494989779823)
                    ·
                      rfl

theorem cell23_2133228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 4].length) (baseStart_2133228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133228 prefixEnd_2133228 := by exact prefixLift 2133228
  have htrace : WordTrace (prefixWord ++ tailWord_2133228) baseStart_2133228 baseEnd_2133228 := by
    simpa [prefixWord, tailWord_2133228, baseEnd_2133228] using wordTrace_append hprefix tailTrace_2133228
  have hstable : (prefixWord ++ tailWord_2133228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133228).length < 2 ^ (prefixWord ++ tailWord_2133228).sum := by decide
  have hdescent : baseEnd_2133228 < baseStart_2133228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133229 : List Nat := [1, 5, 1, 2, 2, 1, 4, 2, 1, 1, 3]
def baseStart_2133229 : Nat := 118140960795 + 2133229 * 2 ^ 59
def prefixEnd_2133229 : Nat := 4983230072969 + 3 ^ 40 * 2133229 * 2
def baseEnd_2133229 : Nat := 1095371823110139465426965

theorem tailTrace_2133229 : CollatzResearch.WordTrace tailWord_2133229 prefixEnd_2133229 1095371823110139465426965 := by
  unfold tailWord_2133229
  simp only [CollatzResearch.WordTrace]
  refine ⟨77805253588683134352794741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51870169059122089568529827 77805253588683134352794741)
  ·
    refine ⟨7294242523939043845574507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77805253588683134352794741 7294242523939043845574507)
    ·
      refine ⟨10941363785908565768361761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7294242523939043845574507 10941363785908565768361761)
      ·
        refine ⟨8206022839431424326271321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10941363785908565768361761 8206022839431424326271321)
        ·
          refine ⟨6154517129573568244703491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8206022839431424326271321 6154517129573568244703491)
          ·
            refine ⟨9231775694360352367055237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6154517129573568244703491 9231775694360352367055237)
            ·
              refine ⟨1730957942692566068822857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9231775694360352367055237 1730957942692566068822857)
              ·
                refine ⟨1298218457019424551617143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1730957942692566068822857 1298218457019424551617143)
                ·
                  refine ⟨1947327685529136827425715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1298218457019424551617143 1947327685529136827425715)
                  ·
                    refine ⟨2920991528293705241138573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1947327685529136827425715 2920991528293705241138573)
                    ·
                      refine ⟨1095371823110139465426965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2920991528293705241138573 1095371823110139465426965)
                      ·
                        rfl

theorem cell23_2133229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_2133229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133229 prefixEnd_2133229 := by exact prefixLift 2133229
  have htrace : WordTrace (prefixWord ++ tailWord_2133229) baseStart_2133229 baseEnd_2133229 := by
    simpa [prefixWord, tailWord_2133229, baseEnd_2133229] using wordTrace_append hprefix tailTrace_2133229
  have hstable : (prefixWord ++ tailWord_2133229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133229).length < 2 ^ (prefixWord ++ tailWord_2133229).sum := by decide
  have hdescent : baseEnd_2133229 < baseStart_2133229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133252 : List Nat := [2, 3, 2, 2, 2, 2, 1, 2, 3, 2, 2]
def baseStart_2133252 : Nat := 118140960795 + 2133252 * 2 ^ 59
def prefixEnd_2133252 : Nat := 4983230072969 + 3 ^ 40 * 2133252 * 2
def baseEnd_2133252 : Nat := 1095383633165192875439359

theorem tailTrace_2133252 : CollatzResearch.WordTrace tailWord_2133252 prefixEnd_2133252 1095383633165192875439359 := by
  unfold tailWord_2133252
  simp only [CollatzResearch.WordTrace]
  refine ⟨38903046233799904640441005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51870728311733206187254673 38903046233799904640441005)
  ·
    refine ⟨14588642337674964240165377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38903046233799904640441005 14588642337674964240165377)
    ·
      refine ⟨10941481753256223180124033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14588642337674964240165377 10941481753256223180124033)
      ·
        refine ⟨8206111314942167385093025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10941481753256223180124033 8206111314942167385093025)
        ·
          refine ⟨6154583486206625538819769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8206111314942167385093025 6154583486206625538819769)
          ·
            refine ⟨4615937614654969154114827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6154583486206625538819769 4615937614654969154114827)
            ·
              refine ⟨6923906421982453731172241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4615937614654969154114827 6923906421982453731172241)
              ·
                refine ⟨5192929816486840298379181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6923906421982453731172241 5192929816486840298379181)
                ·
                  refine ⟨1947348681182565111892193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5192929816486840298379181 1947348681182565111892193)
                  ·
                    refine ⟨1460511510886923833919145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1947348681182565111892193 1460511510886923833919145)
                    ·
                      refine ⟨1095383633165192875439359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1460511510886923833919145 1095383633165192875439359)
                      ·
                        rfl

theorem cell23_2133252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_2133252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133252 prefixEnd_2133252 := by exact prefixLift 2133252
  have htrace : WordTrace (prefixWord ++ tailWord_2133252) baseStart_2133252 baseEnd_2133252 := by
    simpa [prefixWord, tailWord_2133252, baseEnd_2133252] using wordTrace_append hprefix tailTrace_2133252
  have hstable : (prefixWord ++ tailWord_2133252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133252).length < 2 ^ (prefixWord ++ tailWord_2133252).sum := by decide
  have hdescent : baseEnd_2133252 < baseStart_2133252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133266 : List Nat := [3, 2, 4, 2, 2, 1, 2, 1, 1, 5]
def baseStart_2133266 : Nat := 118140960795 + 2133266 * 2 ^ 59
def prefixEnd_2133266 : Nat := 4983230072969 + 3 ^ 40 * 2133266 * 2
def baseEnd_2133266 : Nat := 365130273964785273554765

theorem tailTrace_2133266 : CollatzResearch.WordTrace tailWord_2133266 prefixEnd_2133266 365130273964785273554765 := by
  unfold tailWord_2133266
  simp only [CollatzResearch.WordTrace]
  refine ⟨19451650772387272417972913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51871068726366059781261101 19451650772387272417972913)
  ·
    refine ⟨14588738079290454313479685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19451650772387272417972913 14588738079290454313479685)
    ·
      refine ⟨2735388389866960183777441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14588738079290454313479685 2735388389866960183777441)
      ·
        refine ⟨2051541292400220137833081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2735388389866960183777441 2051541292400220137833081)
        ·
          refine ⟨1538655969300165103374811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2051541292400220137833081 1538655969300165103374811)
          ·
            refine ⟨2307983953950247655062217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1538655969300165103374811 2307983953950247655062217)
            ·
              refine ⟨1730987965462685741296663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2307983953950247655062217 1730987965462685741296663)
              ·
                refine ⟨2596481948194028611944995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1730987965462685741296663 2596481948194028611944995)
                ·
                  refine ⟨3894722922291042917917493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2596481948194028611944995 3894722922291042917917493)
                  ·
                    refine ⟨365130273964785273554765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3894722922291042917917493 365130273964785273554765)
                    ·
                      rfl

theorem cell23_2133266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_2133266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133266 prefixEnd_2133266 := by exact prefixLift 2133266
  have htrace : WordTrace (prefixWord ++ tailWord_2133266) baseStart_2133266 baseEnd_2133266 := by
    simpa [prefixWord, tailWord_2133266, baseEnd_2133266] using wordTrace_append hprefix tailTrace_2133266
  have hstable : (prefixWord ++ tailWord_2133266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133266).length < 2 ^ (prefixWord ++ tailWord_2133266).sum := by decide
  have hdescent : baseEnd_2133266 < baseStart_2133266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133272 : List Nat := [2, 1, 2, 3, 1, 5, 2, 1, 1, 2, 3]
def baseStart_2133272 : Nat := 118140960795 + 2133272 * 2 ^ 59
def prefixEnd_2133272 : Nat := 4983230072969 + 3 ^ 40 * 2133272 * 2
def baseEnd_2133272 : Nat := 1095393902778282797189267

theorem tailTrace_2133272 : CollatzResearch.WordTrace tailWord_2133272 prefixEnd_2133272 1095393902778282797189267 := by
  unfold tailWord_2133272
  simp only [CollatzResearch.WordTrace]
  refine ⟨38903410963763676348305035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51871214618351568464406713 38903410963763676348305035)
  ·
    refine ⟨58355116445645514522457553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38903410963763676348305035 58355116445645514522457553)
    ·
      refine ⟨43766337334234135891843165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58355116445645514522457553 43766337334234135891843165)
      ·
        refine ⟨16412376500337800959441187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43766337334234135891843165 16412376500337800959441187)
        ·
          refine ⟨24618564750506701439161781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16412376500337800959441187 24618564750506701439161781)
          ·
            refine ⟨2307990445360003259921417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24618564750506701439161781 2307990445360003259921417)
            ·
              refine ⟨1730992834020002444941063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2307990445360003259921417 1730992834020002444941063)
              ·
                refine ⟨2596489251030003667411595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1730992834020002444941063 2596489251030003667411595)
                ·
                  refine ⟨3894733876545005501117393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2596489251030003667411595 3894733876545005501117393)
                  ·
                    refine ⟨2921050407408754125838045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3894733876545005501117393 2921050407408754125838045)
                    ·
                      refine ⟨1095393902778282797189267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2921050407408754125838045 1095393902778282797189267)
                      ·
                        rfl

theorem cell23_2133272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 1, 1, 2, 3].length) (baseStart_2133272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133272 prefixEnd_2133272 := by exact prefixLift 2133272
  have htrace : WordTrace (prefixWord ++ tailWord_2133272) baseStart_2133272 baseEnd_2133272 := by
    simpa [prefixWord, tailWord_2133272, baseEnd_2133272] using wordTrace_append hprefix tailTrace_2133272
  have hstable : (prefixWord ++ tailWord_2133272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133272).length < 2 ^ (prefixWord ++ tailWord_2133272).sum := by decide
  have hdescent : baseEnd_2133272 < baseStart_2133272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133285 : List Nat := [1, 3, 1, 2, 4, 2, 1, 1, 4, 1, 3]
def baseStart_2133285 : Nat := 118140960795 + 2133285 * 2 ^ 59
def prefixEnd_2133285 : Nat := 4983230072969 + 3 ^ 40 * 2133285 * 2
def baseEnd_2133285 : Nat := 1095400578026791246326707

theorem tailTrace_2133285 : CollatzResearch.WordTrace tailWord_2133285 prefixEnd_2133285 1095400578026791246326707 := by
  unfold tailWord_2133285
  simp only [CollatzResearch.WordTrace]
  refine ⟨77807296076480255916833309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51871530717653503944555539 77807296076480255916833309)
  ·
    refine ⟨29177736028680095968812491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77807296076480255916833309 29177736028680095968812491)
    ·
      refine ⟨43766604043020143953218737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29177736028680095968812491 43766604043020143953218737)
      ·
        refine ⟨32824953032265107964914053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43766604043020143953218737 32824953032265107964914053)
        ·
          refine ⟨6154678693549707743421385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32824953032265107964914053 6154678693549707743421385)
          ·
            refine ⟨4616009020162280807566039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6154678693549707743421385 4616009020162280807566039)
            ·
              refine ⟨6924013530243421211349059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4616009020162280807566039 6924013530243421211349059)
              ·
                refine ⟨10386020295365131817023589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6924013530243421211349059 10386020295365131817023589)
                ·
                  refine ⟨1947378805380962215691923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10386020295365131817023589 1947378805380962215691923)
                  ·
                    refine ⟨2921068208071443323537885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1947378805380962215691923 2921068208071443323537885)
                    ·
                      refine ⟨1095400578026791246326707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2921068208071443323537885 1095400578026791246326707)
                      ·
                        rfl

theorem cell23_2133285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 4, 1, 3].length) (baseStart_2133285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133285 prefixEnd_2133285 := by exact prefixLift 2133285
  have htrace : WordTrace (prefixWord ++ tailWord_2133285) baseStart_2133285 baseEnd_2133285 := by
    simpa [prefixWord, tailWord_2133285, baseEnd_2133285] using wordTrace_append hprefix tailTrace_2133285
  have hstable : (prefixWord ++ tailWord_2133285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133285).length < 2 ^ (prefixWord ++ tailWord_2133285).sum := by decide
  have hdescent : baseEnd_2133285 < baseStart_2133285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133321 : List Nat := [1, 2, 1, 1, 2, 3, 2, 2, 1, 4, 4]
def baseStart_2133321 : Nat := 118140960795 + 2133321 * 2 ^ 59
def prefixEnd_2133321 : Nat := 4983230072969 + 3 ^ 40 * 2133321 * 2
def baseEnd_2133321 : Nat := 1095419063330353105476541

theorem tailTrace_2133321 : CollatzResearch.WordTrace tailWord_2133321 prefixEnd_2133321 1095419063330353105476541 := by
  unfold tailWord_2133321
  simp only [CollatzResearch.WordTrace]
  refine ⟨77808609104349834065143817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51872406069566556043429211 77808609104349834065143817)
  ·
    refine ⟨58356456828262375548857863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77808609104349834065143817 58356456828262375548857863)
    ·
      refine ⟨87534685242393563323286795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58356456828262375548857863 87534685242393563323286795)
      ·
        refine ⟨131302027863590344984930193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87534685242393563323286795 131302027863590344984930193)
        ·
          refine ⟨98476520897692758738697645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131302027863590344984930193 98476520897692758738697645)
          ·
            refine ⟨36928695336634784527011617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98476520897692758738697645 36928695336634784527011617)
            ·
              refine ⟨27696521502476088395258713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36928695336634784527011617 27696521502476088395258713)
              ·
                refine ⟨20772391126857066296444035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27696521502476088395258713 20772391126857066296444035)
                ·
                  refine ⟨31158586690285599444666053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20772391126857066296444035 31158586690285599444666053)
                  ·
                    refine ⟨5842235004428549895874885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31158586690285599444666053 5842235004428549895874885)
                    ·
                      refine ⟨1095419063330353105476541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5842235004428549895874885 1095419063330353105476541)
                      ·
                        rfl

theorem cell23_2133321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 4, 4].length) (baseStart_2133321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133321 prefixEnd_2133321 := by exact prefixLift 2133321
  have htrace : WordTrace (prefixWord ++ tailWord_2133321) baseStart_2133321 baseEnd_2133321 := by
    simpa [prefixWord, tailWord_2133321, baseEnd_2133321] using wordTrace_append hprefix tailTrace_2133321
  have hstable : (prefixWord ++ tailWord_2133321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133321).length < 2 ^ (prefixWord ++ tailWord_2133321).sum := by decide
  have hdescent : baseEnd_2133321 < baseStart_2133321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133348 : List Nat := [2, 3, 1, 1, 3, 2, 3, 1, 7]
def baseStart_2133348 : Nat := 118140960795 + 2133348 * 2 ^ 59
def prefixEnd_2133348 : Nat := 4983230072969 + 3 ^ 40 * 2133348 * 2
def baseEnd_2133348 : Nat := 121714769700891611093213

theorem tailTrace_2133348 : CollatzResearch.WordTrace tailWord_2133348 prefixEnd_2133348 121714769700891611093213 := by
  unfold tailWord_2133348
  simp only [CollatzResearch.WordTrace]
  refine ⟨38904796937626008838188349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51873062583501345117584465 38904796937626008838188349)
  ·
    refine ⟨14589298851609753314320631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38904796937626008838188349 14589298851609753314320631)
    ·
      refine ⟨21883948277414629971480947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14589298851609753314320631 21883948277414629971480947)
      ·
        refine ⟨32825922416121944957221421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21883948277414629971480947 32825922416121944957221421)
        ·
          refine ⟨12309720906045729358958033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32825922416121944957221421 12309720906045729358958033)
          ·
            refine ⟨9232290679534297019218525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12309720906045729358958033 9232290679534297019218525)
            ·
              refine ⟨3462109004825361382206947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9232290679534297019218525 3462109004825361382206947)
              ·
                refine ⟨5193163507238042073310421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3462109004825361382206947 5193163507238042073310421)
                ·
                  refine ⟨121714769700891611093213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5193163507238042073310421 121714769700891611093213)
                  ·
                    rfl

theorem cell23_2133348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 7].length) (baseStart_2133348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133348 prefixEnd_2133348 := by exact prefixLift 2133348
  have htrace : WordTrace (prefixWord ++ tailWord_2133348) baseStart_2133348 baseEnd_2133348 := by
    simpa [prefixWord, tailWord_2133348, baseEnd_2133348] using wordTrace_append hprefix tailTrace_2133348
  have hstable : (prefixWord ++ tailWord_2133348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133348).length < 2 ^ (prefixWord ++ tailWord_2133348).sum := by decide
  have hdescent : baseEnd_2133348 < baseStart_2133348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133361 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 3, 7]
def baseStart_2133361 : Nat := 118140960795 + 2133361 * 2 ^ 59
def prefixEnd_2133361 : Nat := 4983230072969 + 3 ^ 40 * 2133361 * 2
def baseEnd_2133361 : Nat := 365146534185510982992119

theorem tailTrace_2133361 : CollatzResearch.WordTrace tailWord_2133361 prefixEnd_2133361 365146534185510982992119 := by
  unfold tailWord_2133361
  simp only [CollatzResearch.WordTrace]
  refine ⟨77810068024204920896599937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51873378682803280597733291 77810068024204920896599937)
  ·
    refine ⟨58357551018153690672449953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77810068024204920896599937 58357551018153690672449953)
    ·
      refine ⟨43768163263615268004337465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58357551018153690672449953 43768163263615268004337465)
      ·
        refine ⟨32826122447711451003253099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43768163263615268004337465 32826122447711451003253099)
        ·
          refine ⟨49239183671567176504879649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32826122447711451003253099 49239183671567176504879649)
          ·
            refine ⟨36929387753675382378659737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49239183671567176504879649 36929387753675382378659737)
            ·
              refine ⟨27697040815256536783994803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36929387753675382378659737 27697040815256536783994803)
              ·
                refine ⟨41545561222884805175992205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27697040815256536783994803 41545561222884805175992205)
                ·
                  refine ⟨15579585458581801940997077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41545561222884805175992205 15579585458581801940997077)
                  ·
                    refine ⟨365146534185510982992119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15579585458581801940997077 365146534185510982992119)
                    ·
                      rfl

theorem cell23_2133361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 7].length) (baseStart_2133361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133361 prefixEnd_2133361 := by exact prefixLift 2133361
  have htrace : WordTrace (prefixWord ++ tailWord_2133361) baseStart_2133361 baseEnd_2133361 := by
    simpa [prefixWord, tailWord_2133361, baseEnd_2133361] using wordTrace_append hprefix tailTrace_2133361
  have hstable : (prefixWord ++ tailWord_2133361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133361).length < 2 ^ (prefixWord ++ tailWord_2133361).sum := by decide
  have hdescent : baseEnd_2133361 < baseStart_2133361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133371 : List Nat := [1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 7]
def baseStart_2133371 : Nat := 118140960795 + 2133371 * 2 ^ 59
def prefixEnd_2133371 : Nat := 4983230072969 + 3 ^ 40 * 2133371 * 2
def baseEnd_2133371 : Nat := 1095444737363077909851311

theorem tailTrace_2133371 : CollatzResearch.WordTrace tailWord_2133371 prefixEnd_2133371 1095444737363077909851311 := by
  unfold tailWord_2133371
  simp only [CollatzResearch.WordTrace]
  refine ⟨77810432754168692604463967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51873621836112461736309311 77810432754168692604463967)
  ·
    refine ⟨116715649131253038906695951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77810432754168692604463967 116715649131253038906695951)
    ·
      refine ⟨175073473696879558360043927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116715649131253038906695951 175073473696879558360043927)
      ·
        refine ⟨262610210545319337540065891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175073473696879558360043927 262610210545319337540065891)
        ·
          refine ⟨393915315817979006310098837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262610210545319337540065891 393915315817979006310098837)
          ·
            refine ⟨18464780428967765920785883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 393915315817979006310098837 18464780428967765920785883)
            ·
              refine ⟨27697170643451648881178825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18464780428967765920785883 27697170643451648881178825)
              ·
                refine ⟨20772877982588736660884119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27697170643451648881178825 20772877982588736660884119)
                ·
                  refine ⟨31159316973883104991326179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20772877982588736660884119 31159316973883104991326179)
                  ·
                    refine ⟨46738975460824657486989269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31159316973883104991326179 46738975460824657486989269)
                    ·
                      refine ⟨1095444737363077909851311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 46738975460824657486989269 1095444737363077909851311)
                      ·
                        rfl

theorem cell23_2133371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 7].length) (baseStart_2133371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133371 prefixEnd_2133371 := by exact prefixLift 2133371
  have htrace : WordTrace (prefixWord ++ tailWord_2133371) baseStart_2133371 baseEnd_2133371 := by
    simpa [prefixWord, tailWord_2133371, baseEnd_2133371] using wordTrace_append hprefix tailTrace_2133371
  have hstable : (prefixWord ++ tailWord_2133371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133371).length < 2 ^ (prefixWord ++ tailWord_2133371).sum := by decide
  have hdescent : baseEnd_2133371 < baseStart_2133371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133425 : List Nat := [1, 2, 2, 4, 1, 1, 3, 2, 3, 4]
def baseStart_2133425 : Nat := 118140960795 + 2133425 * 2 ^ 59
def prefixEnd_2133425 : Nat := 4983230072969 + 3 ^ 40 * 2133425 * 2
def baseEnd_2133425 : Nat := 365157488439473566192021

theorem tailTrace_2133425 : CollatzResearch.WordTrace tailWord_2133425 prefixEnd_2133425 365157488439473566192021 := by
  unfold tailWord_2133425
  simp only [CollatzResearch.WordTrace]
  refine ⟨77812402295973059826929729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51874934863982039884619819 77812402295973059826929729)
  ·
    refine ⟨58359301721979794870197297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77812402295973059826929729 58359301721979794870197297)
    ·
      refine ⟨43769476291484846152647973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58359301721979794870197297 43769476291484846152647973)
      ·
        refine ⟨8206776804653408653621495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43769476291484846152647973 8206776804653408653621495)
        ·
          refine ⟨12310165206980112980432243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8206776804653408653621495 12310165206980112980432243)
          ·
            refine ⟨18465247810470169470648365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12310165206980112980432243 18465247810470169470648365)
            ·
              refine ⟨6924467928926313551493137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18465247810470169470648365 6924467928926313551493137)
              ·
                refine ⟨5193350946694735163619853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6924467928926313551493137 5193350946694735163619853)
                ·
                  refine ⟨1947506605010525686357445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5193350946694735163619853 1947506605010525686357445)
                  ·
                    refine ⟨365157488439473566192021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1947506605010525686357445 365157488439473566192021)
                    ·
                      rfl

theorem cell23_2133425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 3, 4].length) (baseStart_2133425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133425 prefixEnd_2133425 := by exact prefixLift 2133425
  have htrace : WordTrace (prefixWord ++ tailWord_2133425) baseStart_2133425 baseEnd_2133425 := by
    simpa [prefixWord, tailWord_2133425, baseEnd_2133425] using wordTrace_append hprefix tailTrace_2133425
  have hstable : (prefixWord ++ tailWord_2133425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133425).length < 2 ^ (prefixWord ++ tailWord_2133425).sum := by decide
  have hdescent : baseEnd_2133425 < baseStart_2133425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133438 : List Nat := [4, 2, 1, 1, 1, 1, 1, 4, 8]
def baseStart_2133438 : Nat := 118140960795 + 2133438 * 2 ^ 59
def prefixEnd_2133438 : Nat := 4983230072969 + 3 ^ 40 * 2133438 * 2
def baseEnd_2133438 : Nat := 121719904507436571968167

theorem tailTrace_2133438 : CollatzResearch.WordTrace tailWord_2133438 prefixEnd_2133438 121719904507436571968167 := by
  unfold tailWord_2133438
  simp only [CollatzResearch.WordTrace]
  refine ⟨9726609555615745380894121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51875250963283975364768645 9726609555615745380894121)
  ·
    refine ⟨7294957166711809035670591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9726609555615745380894121 7294957166711809035670591)
    ·
      refine ⟨10942435750067713553505887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7294957166711809035670591 10942435750067713553505887)
      ·
        refine ⟨16413653625101570330258831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10942435750067713553505887 16413653625101570330258831)
        ·
          refine ⟨24620480437652355495388247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16413653625101570330258831 24620480437652355495388247)
          ·
            refine ⟨36930720656478533243082371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24620480437652355495388247 36930720656478533243082371)
            ·
              refine ⟨55396080984717799864623557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36930720656478533243082371 55396080984717799864623557)
              ·
                refine ⟨10386765184634587474616917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55396080984717799864623557 10386765184634587474616917)
                ·
                  refine ⟨121719904507436571968167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10386765184634587474616917 121719904507436571968167)
                  ·
                    rfl

theorem cell23_2133438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_2133438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133438 prefixEnd_2133438 := by exact prefixLift 2133438
  have htrace : WordTrace (prefixWord ++ tailWord_2133438) baseStart_2133438 baseEnd_2133438 := by
    simpa [prefixWord, tailWord_2133438, baseEnd_2133438] using wordTrace_append hprefix tailTrace_2133438
  have hstable : (prefixWord ++ tailWord_2133438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133438).length < 2 ^ (prefixWord ++ tailWord_2133438).sum := by decide
  have hdescent : baseEnd_2133438 < baseStart_2133438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133498 : List Nat := [3, 1, 1, 1, 1, 2, 4, 1, 3, 6]
def baseStart_2133498 : Nat := 118140960795 + 2133498 * 2 ^ 59
def prefixEnd_2133498 : Nat := 4983230072969 + 3 ^ 40 * 2133498 * 2
def baseEnd_2133498 : Nat := 365169983135399637654409

theorem tailTrace_2133498 : CollatzResearch.WordTrace tailWord_2133498 prefixEnd_2133498 365169983135399637654409 := by
  unfold tailWord_2133498
  simp only [CollatzResearch.WordTrace]
  refine ⟨19453766206177148323584287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51876709883139062196224765 19453766206177148323584287)
  ·
    refine ⟨29180649309265722485376431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19453766206177148323584287 29180649309265722485376431)
    ·
      refine ⟨43770973963898583728064647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29180649309265722485376431 43770973963898583728064647)
      ·
        refine ⟨65656460945847875592096971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43770973963898583728064647 65656460945847875592096971)
        ·
          refine ⟨98484691418771813388145457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65656460945847875592096971 98484691418771813388145457)
          ·
            refine ⟨73863518564078860041109093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98484691418771813388145457 73863518564078860041109093)
            ·
              refine ⟨13849409730764786257707955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73863518564078860041109093 13849409730764786257707955)
              ·
                refine ⟨20774114596147179386561933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13849409730764786257707955 20774114596147179386561933)
                ·
                  refine ⟨7790292973555192269960725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20774114596147179386561933 7790292973555192269960725)
                  ·
                    refine ⟨365169983135399637654409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7790292973555192269960725 365169983135399637654409)
                    ·
                      rfl

theorem cell23_2133498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 3, 6].length) (baseStart_2133498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133498 prefixEnd_2133498 := by exact prefixLift 2133498
  have htrace : WordTrace (prefixWord ++ tailWord_2133498) baseStart_2133498 baseEnd_2133498 := by
    simpa [prefixWord, tailWord_2133498, baseEnd_2133498] using wordTrace_append hprefix tailTrace_2133498
  have hstable : (prefixWord ++ tailWord_2133498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133498).length < 2 ^ (prefixWord ++ tailWord_2133498).sum := by decide
  have hdescent : baseEnd_2133498 < baseStart_2133498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133510 : List Nat := [6, 2, 1, 1, 3, 1, 1, 1, 3, 4]
def baseStart_2133510 : Nat := 118140960795 + 2133510 * 2 ^ 59
def prefixEnd_2133510 : Nat := 4983230072969 + 3 ^ 40 * 2133510 * 2
def baseEnd_2133510 : Nat := 365172037058017622004391

theorem tailTrace_2133510 : CollatzResearch.WordTrace tailWord_2133510 prefixEnd_2133510 365172037058017622004391 := by
  unfold tailWord_2133510
  simp only [CollatzResearch.WordTrace]
  refine ⟨2431734453145784979492937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 51877001667110079562515989 2431734453145784979492937)
  ·
    refine ⟨1823800839859338734619703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2431734453145784979492937 1823800839859338734619703)
    ·
      refine ⟨2735701259789008101929555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1823800839859338734619703 2735701259789008101929555)
      ·
        refine ⟨4103551889683512152894333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2735701259789008101929555 4103551889683512152894333)
        ·
          refine ⟨1538831958631317057335375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4103551889683512152894333 1538831958631317057335375)
          ·
            refine ⟨2308247937946975586003063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1538831958631317057335375 2308247937946975586003063)
            ·
              refine ⟨3462371906920463379004595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2308247937946975586003063 3462371906920463379004595)
              ·
                refine ⟨5193557860380695068506893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3462371906920463379004595 5193557860380695068506893)
                ·
                  refine ⟨1947584197642760650690085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5193557860380695068506893 1947584197642760650690085)
                  ·
                    refine ⟨365172037058017622004391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1947584197642760650690085 365172037058017622004391)
                    ·
                      rfl

theorem cell23_2133510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_2133510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133510 prefixEnd_2133510 := by exact prefixLift 2133510
  have htrace : WordTrace (prefixWord ++ tailWord_2133510) baseStart_2133510 baseEnd_2133510 := by
    simpa [prefixWord, tailWord_2133510, baseEnd_2133510] using wordTrace_append hprefix tailTrace_2133510
  have hstable : (prefixWord ++ tailWord_2133510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133510).length < 2 ^ (prefixWord ++ tailWord_2133510).sum := by decide
  have hdescent : baseEnd_2133510 < baseStart_2133510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133516 : List Nat := [2, 2, 1, 2, 6, 1, 1, 1, 3, 1, 3]
def baseStart_2133516 : Nat := 118140960795 + 2133516 * 2 ^ 59
def prefixEnd_2133516 : Nat := 4983230072969 + 3 ^ 40 * 2133516 * 2
def baseEnd_2133516 : Nat := 1095519192057979842538145

theorem tailTrace_2133516 : CollatzResearch.WordTrace tailWord_2133516 prefixEnd_2133516 1095519192057979842538145 := by
  unfold tailWord_2133516
  simp only [CollatzResearch.WordTrace]
  refine ⟨38907860669321691184246201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51877147559095588245661601 38907860669321691184246201)
  ·
    refine ⟨29180895501991268388184651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38907860669321691184246201 29180895501991268388184651)
    ·
      refine ⟨43771343252986902582276977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29180895501991268388184651 43771343252986902582276977)
      ·
        refine ⟨32828507439740176936707733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43771343252986902582276977 32828507439740176936707733)
        ·
          refine ⟨1538836286237820793908175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 32828507439740176936707733 1538836286237820793908175)
          ·
            refine ⟨2308254429356731190862263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1538836286237820793908175 2308254429356731190862263)
            ·
              refine ⟨3462381644035096786293395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2308254429356731190862263 3462381644035096786293395)
              ·
                refine ⟨5193572466052645179440093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3462381644035096786293395 5193572466052645179440093)
                ·
                  refine ⟨1947589674769741942290035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5193572466052645179440093 1947589674769741942290035)
                  ·
                    refine ⟨2921384512154612913435053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1947589674769741942290035 2921384512154612913435053)
                    ·
                      refine ⟨1095519192057979842538145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2921384512154612913435053 1095519192057979842538145)
                      ·
                        rfl

theorem cell23_2133516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 3, 1, 3].length) (baseStart_2133516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133516 prefixEnd_2133516 := by exact prefixLift 2133516
  have htrace : WordTrace (prefixWord ++ tailWord_2133516) baseStart_2133516 baseEnd_2133516 := by
    simpa [prefixWord, tailWord_2133516, baseEnd_2133516] using wordTrace_append hprefix tailTrace_2133516
  have hstable : (prefixWord ++ tailWord_2133516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133516).length < 2 ^ (prefixWord ++ tailWord_2133516).sum := by decide
  have hdescent : baseEnd_2133516 < baseStart_2133516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133525 : List Nat := [1, 3, 2, 1, 3, 2, 2, 2, 1, 1, 5]
def baseStart_2133525 : Nat := 118140960795 + 2133525 * 2 ^ 59
def prefixEnd_2133525 : Nat := 4983230072969 + 3 ^ 40 * 2133525 * 2
def baseEnd_2133525 : Nat := 1095523813383870307325603

theorem tailTrace_2133525 : CollatzResearch.WordTrace tailWord_2133525 prefixEnd_2133525 1095523813383870307325603 := by
  unfold tailWord_2133525
  simp only [CollatzResearch.WordTrace]
  refine ⟨77816049595610776905570029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51877366397073851270380019 77816049595610776905570029)
  ·
    refine ⟨29181018598354041339588761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77816049595610776905570029 29181018598354041339588761)
    ·
      refine ⟨21885763948765531004691571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29181018598354041339588761 21885763948765531004691571)
      ·
        refine ⟨32828645923148296507037357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21885763948765531004691571 32828645923148296507037357)
        ·
          refine ⟨12310742221180611190139009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32828645923148296507037357 12310742221180611190139009)
          ·
            refine ⟨9233056665885458392604257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12310742221180611190139009 9233056665885458392604257)
            ·
              refine ⟨6924792499414093794453193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9233056665885458392604257 6924792499414093794453193)
              ·
                refine ⟨5193594374560570345839895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6924792499414093794453193 5193594374560570345839895)
                ·
                  refine ⟨7790391561840855518759843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5193594374560570345839895 7790391561840855518759843)
                  ·
                    refine ⟨11685587342761283278139765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7790391561840855518759843 11685587342761283278139765)
                    ·
                      refine ⟨1095523813383870307325603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11685587342761283278139765 1095523813383870307325603)
                      ·
                        rfl

theorem cell23_2133525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_2133525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133525 prefixEnd_2133525 := by exact prefixLift 2133525
  have htrace : WordTrace (prefixWord ++ tailWord_2133525) baseStart_2133525 baseEnd_2133525 := by
    simpa [prefixWord, tailWord_2133525, baseEnd_2133525] using wordTrace_append hprefix tailTrace_2133525
  have hstable : (prefixWord ++ tailWord_2133525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133525).length < 2 ^ (prefixWord ++ tailWord_2133525).sum := by decide
  have hdescent : baseEnd_2133525 < baseStart_2133525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133532 : List Nat := [2, 2, 3, 1, 2, 1, 3, 3, 2, 4]
def baseStart_2133532 : Nat := 118140960795 + 2133532 * 2 ^ 59
def prefixEnd_2133532 : Nat := 4983230072969 + 3 ^ 40 * 2133532 * 2
def baseEnd_2133532 : Nat := 365175802582817259979357

theorem tailTrace_2133532 : CollatzResearch.WordTrace tailWord_2133532 prefixEnd_2133532 365175802582817259979357 := by
  unfold tailWord_2133532
  simp only [CollatzResearch.WordTrace]
  refine ⟨38908152453292708550537425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51877536604390278067383233 38908152453292708550537425)
  ·
    refine ⟨29181114339969531412903069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38908152453292708550537425 29181114339969531412903069)
    ·
      refine ⟨10942917877488574279838651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29181114339969531412903069 10942917877488574279838651)
      ·
        refine ⟨16414376816232861419757977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10942917877488574279838651 16414376816232861419757977)
        ·
          refine ⟨12310782612174646064818483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16414376816232861419757977 12310782612174646064818483)
          ·
            refine ⟨18466173918261969097227725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12310782612174646064818483 18466173918261969097227725)
            ·
              refine ⟨6924815219348238411460397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18466173918261969097227725 6924815219348238411460397)
              ·
                refine ⟨2596805707255589404297649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6924815219348238411460397 2596805707255589404297649)
                ·
                  refine ⟨1947604280441692053223237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2596805707255589404297649 1947604280441692053223237)
                  ·
                    refine ⟨365175802582817259979357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1947604280441692053223237 365175802582817259979357)
                    ·
                      rfl

theorem cell23_2133532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_2133532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133532 prefixEnd_2133532 := by exact prefixLift 2133532
  have htrace : WordTrace (prefixWord ++ tailWord_2133532) baseStart_2133532 baseEnd_2133532 := by
    simpa [prefixWord, tailWord_2133532, baseEnd_2133532] using wordTrace_append hprefix tailTrace_2133532
  have hstable : (prefixWord ++ tailWord_2133532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133532).length < 2 ^ (prefixWord ++ tailWord_2133532).sum := by decide
  have hdescent : baseEnd_2133532 < baseStart_2133532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133539 : List Nat := [1, 1, 1, 4, 5, 2, 1, 2, 1, 1, 4]
def baseStart_2133539 : Nat := 118140960795 + 2133539 * 2 ^ 59
def prefixEnd_2133539 : Nat := 4983230072969 + 3 ^ 40 * 2133539 * 2
def baseEnd_2133539 : Nat := 1095531002113033252550539

theorem tailTrace_2133539 : CollatzResearch.WordTrace tailWord_2133539 prefixEnd_2133539 1095531002113033252550539 := by
  unfold tailWord_2133539
  simp only [CollatzResearch.WordTrace]
  refine ⟨77816560217560057296579671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51877706811706704864386447 77816560217560057296579671)
  ·
    refine ⟨116724840326340085944869507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77816560217560057296579671 116724840326340085944869507)
    ·
      refine ⟨175087260489510128917304261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116724840326340085944869507 175087260489510128917304261)
      ·
        refine ⟨32828861341783149171994549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 175087260489510128917304261 32828861341783149171994549)
        ·
          refine ⟨3077705750792170234874489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32828861341783149171994549 3077705750792170234874489)
          ·
            refine ⟨2308279313094127676155867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3077705750792170234874489 2308279313094127676155867)
            ·
              refine ⟨3462418969641191514233801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2308279313094127676155867 3462418969641191514233801)
              ·
                refine ⟨2596814227230893635675351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3462418969641191514233801 2596814227230893635675351)
                ·
                  refine ⟨3895221340846340453513027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2596814227230893635675351 3895221340846340453513027)
                  ·
                    refine ⟨5842832011269510680269541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3895221340846340453513027 5842832011269510680269541)
                    ·
                      refine ⟨1095531002113033252550539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5842832011269510680269541 1095531002113033252550539)
                      ·
                        rfl

theorem cell23_2133539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 2, 1, 1, 4].length) (baseStart_2133539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133539 prefixEnd_2133539 := by exact prefixLift 2133539
  have htrace : WordTrace (prefixWord ++ tailWord_2133539) baseStart_2133539 baseEnd_2133539 := by
    simpa [prefixWord, tailWord_2133539, baseEnd_2133539] using wordTrace_append hprefix tailTrace_2133539
  have hstable : (prefixWord ++ tailWord_2133539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133539).length < 2 ^ (prefixWord ++ tailWord_2133539).sum := by decide
  have hdescent : baseEnd_2133539 < baseStart_2133539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133555 : List Nat := [1, 1, 1, 2, 4, 3, 1, 1, 3, 3, 3]
def baseStart_2133555 : Nat := 118140960795 + 2133555 * 2 ^ 59
def prefixEnd_2133555 : Nat := 4983230072969 + 3 ^ 40 * 2133555 * 2
def baseEnd_2133555 : Nat := 1095539217803505189950465

theorem tailTrace_2133555 : CollatzResearch.WordTrace tailWord_2133555 prefixEnd_2133555 1095539217803505189950465 := by
  unfold tailWord_2133555
  simp only [CollatzResearch.WordTrace]
  refine ⟨77817143785502092029162119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51878095857001394686108079 77817143785502092029162119)
  ·
    refine ⟨116725715678253138043743179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77817143785502092029162119 116725715678253138043743179)
    ·
      refine ⟨175088573517379707065614769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116725715678253138043743179 175088573517379707065614769)
      ·
        refine ⟨131316430138034780299211077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175088573517379707065614769 131316430138034780299211077)
        ·
          refine ⟨24621830650881521306102077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 131316430138034780299211077 24621830650881521306102077)
          ·
            refine ⟨9233186494080570489788279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24621830650881521306102077 9233186494080570489788279)
            ·
              refine ⟨13849779741120855734682419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9233186494080570489788279 13849779741120855734682419)
              ·
                refine ⟨20774669611681283602023629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13849779741120855734682419 20774669611681283602023629)
                ·
                  refine ⟨7790501104380481350758861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20774669611681283602023629 7790501104380481350758861)
                  ·
                    refine ⟨2921437914142680506534573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7790501104380481350758861 2921437914142680506534573)
                    ·
                      refine ⟨1095539217803505189950465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2921437914142680506534573 1095539217803505189950465)
                      ·
                        rfl

theorem cell23_2133555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 3, 3].length) (baseStart_2133555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133555 prefixEnd_2133555 := by exact prefixLift 2133555
  have htrace : WordTrace (prefixWord ++ tailWord_2133555) baseStart_2133555 baseEnd_2133555 := by
    simpa [prefixWord, tailWord_2133555, baseEnd_2133555] using wordTrace_append hprefix tailTrace_2133555
  have hstable : (prefixWord ++ tailWord_2133555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133555).length < 2 ^ (prefixWord ++ tailWord_2133555).sum := by decide
  have hdescent : baseEnd_2133555 < baseStart_2133555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133559 : List Nat := [1, 1, 3, 1, 2, 5, 3, 1, 1, 2, 3]
def baseStart_2133559 : Nat := 118140960795 + 2133559 * 2 ^ 59
def prefixEnd_2133559 : Nat := 4983230072969 + 3 ^ 40 * 2133559 * 2
def baseEnd_2133559 : Nat := 1095541271726123174300447

theorem tailTrace_2133559 : CollatzResearch.WordTrace tailWord_2133559 prefixEnd_2133559 1095541271726123174300447 := by
  unfold tailWord_2133559
  simp only [CollatzResearch.WordTrace]
  refine ⟨77817289677487600712307731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51878193118325067141538487 77817289677487600712307731)
  ·
    refine ⟨116725934516231401068461597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77817289677487600712307731 116725934516231401068461597)
    ·
      refine ⟨43772225443586775400673099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116725934516231401068461597 43772225443586775400673099)
      ·
        refine ⟨65658338165380163101009649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43772225443586775400673099 65658338165380163101009649)
        ·
          refine ⟨49243753624035122325757237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65658338165380163101009649 49243753624035122325757237)
          ·
            refine ⟨4616601902253292718039741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49243753624035122325757237 4616601902253292718039741)
            ·
              refine ⟨1731225713344984769264903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4616601902253292718039741 1731225713344984769264903)
              ·
                refine ⟨2596838570017477153897355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1731225713344984769264903 2596838570017477153897355)
                ·
                  refine ⟨3895257855026215730846033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2596838570017477153897355 3895257855026215730846033)
                  ·
                    refine ⟨2921443391269661798134525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3895257855026215730846033 2921443391269661798134525)
                    ·
                      refine ⟨1095541271726123174300447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2921443391269661798134525 1095541271726123174300447)
                      ·
                        rfl

theorem cell23_2133559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 1, 1, 2, 3].length) (baseStart_2133559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133559 prefixEnd_2133559 := by exact prefixLift 2133559
  have htrace : WordTrace (prefixWord ++ tailWord_2133559) baseStart_2133559 baseEnd_2133559 := by
    simpa [prefixWord, tailWord_2133559, baseEnd_2133559] using wordTrace_append hprefix tailTrace_2133559
  have hstable : (prefixWord ++ tailWord_2133559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133559).length < 2 ^ (prefixWord ++ tailWord_2133559).sum := by decide
  have hdescent : baseEnd_2133559 < baseStart_2133559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133590 : List Nat := [5, 2, 2, 2, 1, 1, 1, 2, 3, 2, 2]
def baseStart_2133590 : Nat := 118140960795 + 2133590 * 2 ^ 59
def prefixEnd_2133590 : Nat := 4983230072969 + 3 ^ 40 * 2133590 * 2
def baseEnd_2133590 : Nat := 1095557189626412553012805

theorem tailTrace_2133590 : CollatzResearch.WordTrace tailWord_2133590 prefixEnd_2133590 1095557189626412553012805 := by
  unfold tailWord_2133590
  simp only [CollatzResearch.WordTrace]
  refine ⟨4863651271273455812917889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51878946893583528671124149 4863651271273455812917889)
  ·
    refine ⟨3647738453455091859688417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4863651271273455812917889 3647738453455091859688417)
    ·
      refine ⟨2735803840091318894766313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3647738453455091859688417 2735803840091318894766313)
      ·
        refine ⟨2051852880068489171074735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2735803840091318894766313 2051852880068489171074735)
        ·
          refine ⟨3077779320102733756612103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2051852880068489171074735 3077779320102733756612103)
          ·
            refine ⟨4616668980154100634918155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3077779320102733756612103 4616668980154100634918155)
            ·
              refine ⟨6925003470231150952377233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4616668980154100634918155 6925003470231150952377233)
              ·
                refine ⟨5193752602673363214282925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6925003470231150952377233 5193752602673363214282925)
                ·
                  refine ⟨1947657226002511205356097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5193752602673363214282925 1947657226002511205356097)
                  ·
                    refine ⟨1460742919501883404017073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1947657226002511205356097 1460742919501883404017073)
                    ·
                      refine ⟨1095557189626412553012805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1460742919501883404017073 1095557189626412553012805)
                      ·
                        rfl

theorem cell23_2133590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_2133590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133590 prefixEnd_2133590 := by exact prefixLift 2133590
  have htrace : WordTrace (prefixWord ++ tailWord_2133590) baseStart_2133590 baseEnd_2133590 := by
    simpa [prefixWord, tailWord_2133590, baseEnd_2133590] using wordTrace_append hprefix tailTrace_2133590
  have hstable : (prefixWord ++ tailWord_2133590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133590).length < 2 ^ (prefixWord ++ tailWord_2133590).sum := by decide
  have hdescent : baseEnd_2133590 < baseStart_2133590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133616 : List Nat := [2, 1, 1, 1, 6, 1, 4, 1, 1, 3, 2]
def baseStart_2133616 : Nat := 118140960795 + 2133616 * 2 ^ 59
def prefixEnd_2133616 : Nat := 4983230072969 + 3 ^ 40 * 2133616 * 2
def baseEnd_2133616 : Nat := 1095570540123429451287685

theorem tailTrace_2133616 : CollatzResearch.WordTrace tailWord_2133616 prefixEnd_2133616 1095570540123429451287685 := by
  unfold tailWord_2133616
  simp only [CollatzResearch.WordTrace]
  refine ⟨38909684319140549723566351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51879579092187399631421801 38909684319140549723566351)
  ·
    refine ⟨58364526478710824585349527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38909684319140549723566351 58364526478710824585349527)
    ·
      refine ⟨87546789718066236878024291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58364526478710824585349527 87546789718066236878024291)
      ·
        refine ⟨131320184577099355317036437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87546789718066236878024291 131320184577099355317036437)
        ·
          refine ⟨6155633652051532280486083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 131320184577099355317036437 6155633652051532280486083)
          ·
            refine ⟨9233450478077298420729125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6155633652051532280486083 9233450478077298420729125)
            ·
              refine ⟨1731271964639493453886711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9233450478077298420729125 1731271964639493453886711)
              ·
                refine ⟨2596907946959240180830067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1731271964639493453886711 2596907946959240180830067)
                ·
                  refine ⟨3895361920438860271245101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2596907946959240180830067 3895361920438860271245101)
                  ·
                    refine ⟨1460760720164572601716913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3895361920438860271245101 1460760720164572601716913)
                    ·
                      refine ⟨1095570540123429451287685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1460760720164572601716913 1095570540123429451287685)
                      ·
                        rfl

theorem cell23_2133616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 1, 1, 3, 2].length) (baseStart_2133616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133616 prefixEnd_2133616 := by exact prefixLift 2133616
  have htrace : WordTrace (prefixWord ++ tailWord_2133616) baseStart_2133616 baseEnd_2133616 := by
    simpa [prefixWord, tailWord_2133616, baseEnd_2133616] using wordTrace_append hprefix tailTrace_2133616
  have hstable : (prefixWord ++ tailWord_2133616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133616).length < 2 ^ (prefixWord ++ tailWord_2133616).sum := by decide
  have hdescent : baseEnd_2133616 < baseStart_2133616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133622 : List Nat := [5, 1, 1, 2, 2, 1, 1, 2, 2, 6]
def baseStart_2133622 : Nat := 118140960795 + 2133622 * 2 ^ 59
def prefixEnd_2133622 : Nat := 4983230072969 + 3 ^ 40 * 2133622 * 2
def baseEnd_2133622 : Nat := 365191207002452142604219

theorem tailTrace_2133622 : CollatzResearch.WordTrace tailWord_2133622 prefixEnd_2133622 365191207002452142604219 := by
  unfold tailWord_2133622
  simp only [CollatzResearch.WordTrace]
  refine ⟨4863724217266210154490695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51879724984172908314567413 4863724217266210154490695)
  ·
    refine ⟨7295586325899315231736043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4863724217266210154490695 7295586325899315231736043)
    ·
      refine ⟨10943379488848972847604065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7295586325899315231736043 10943379488848972847604065)
      ·
        refine ⟨8207534616636729635703049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10943379488848972847604065 8207534616636729635703049)
        ·
          refine ⟨6155650962477547226777287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8207534616636729635703049 6155650962477547226777287)
          ·
            refine ⟨9233476443716320840165931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6155650962477547226777287 9233476443716320840165931)
            ·
              refine ⟨13850214665574481260248897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9233476443716320840165931 13850214665574481260248897)
              ·
                refine ⟨10387660999180860945186673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13850214665574481260248897 10387660999180860945186673)
                ·
                  refine ⟨7790745749385645708890005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10387660999180860945186673 7790745749385645708890005)
                  ·
                    refine ⟨365191207002452142604219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7790745749385645708890005 365191207002452142604219)
                    ·
                      rfl

theorem cell23_2133622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_2133622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133622 prefixEnd_2133622 := by exact prefixLift 2133622
  have htrace : WordTrace (prefixWord ++ tailWord_2133622) baseStart_2133622 baseEnd_2133622 := by
    simpa [prefixWord, tailWord_2133622, baseEnd_2133622] using wordTrace_append hprefix tailTrace_2133622
  have hstable : (prefixWord ++ tailWord_2133622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133622).length < 2 ^ (prefixWord ++ tailWord_2133622).sum := by decide
  have hdescent : baseEnd_2133622 < baseStart_2133622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133625 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 4, 2, 4]
def baseStart_2133625 : Nat := 118140960795 + 2133625 * 2 ^ 59
def prefixEnd_2133625 : Nat := 4983230072969 + 3 ^ 40 * 2133625 * 2
def baseEnd_2133625 : Nat := 1095575161449319916075143

theorem tailTrace_2133625 : CollatzResearch.WordTrace tailWord_2133625 prefixEnd_2133625 1095575161449319916075143 := by
  unfold tailWord_2133625
  simp only [CollatzResearch.WordTrace]
  refine ⟨77819696895248493984210329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51879797930165662656140219 77819696895248493984210329)
  ·
    refine ⟨58364772671436370488157747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77819696895248493984210329 58364772671436370488157747)
    ·
      refine ⟨87547159007154555732236621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58364772671436370488157747 87547159007154555732236621)
      ·
        refine ⟨32830184627682958399588733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87547159007154555732236621 32830184627682958399588733)
        ·
          refine ⟨12311319235381109399845775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32830184627682958399588733 12311319235381109399845775)
          ·
            refine ⟨18466978853071664099768663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12311319235381109399845775 18466978853071664099768663)
            ·
              refine ⟨27700468279607496149652995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18466978853071664099768663 27700468279607496149652995)
              ·
                refine ⟨41550702419411244224479493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27700468279607496149652995 41550702419411244224479493)
                ·
                  refine ⟨7790756703639608292089905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41550702419411244224479493 7790756703639608292089905)
                  ·
                    refine ⟨5843067527729706219067429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7790756703639608292089905 5843067527729706219067429)
                    ·
                      refine ⟨1095575161449319916075143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5843067527729706219067429 1095575161449319916075143)
                      ·
                        rfl

theorem cell23_2133625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_2133625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133625 prefixEnd_2133625 := by exact prefixLift 2133625
  have htrace : WordTrace (prefixWord ++ tailWord_2133625) baseStart_2133625 baseEnd_2133625 := by
    simpa [prefixWord, tailWord_2133625, baseEnd_2133625] using wordTrace_append hprefix tailTrace_2133625
  have hstable : (prefixWord ++ tailWord_2133625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133625).length < 2 ^ (prefixWord ++ tailWord_2133625).sum := by decide
  have hdescent : baseEnd_2133625 < baseStart_2133625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133642 : List Nat := [3, 1, 2, 3, 2, 1, 2, 1, 2, 2, 4]
def baseStart_2133642 : Nat := 118140960795 + 2133642 * 2 ^ 59
def prefixEnd_2133642 : Nat := 4983230072969 + 3 ^ 40 * 2133642 * 2
def baseEnd_2133642 : Nat := 1095583890620446349562565

theorem tailTrace_2133642 : CollatzResearch.WordTrace tailWord_2133642 prefixEnd_2133642 1095583890620446349562565 := by
  unfold tailWord_2133642
  simp only [CollatzResearch.WordTrace]
  refine ⟨19455079234046726471894795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51880211290791270591719453 19455079234046726471894795)
  ·
    refine ⟨29182618851070089707842193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19455079234046726471894795 29182618851070089707842193)
    ·
      refine ⟨21886964138302567280881645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29182618851070089707842193 21886964138302567280881645)
      ·
        refine ⟨8207611551863462730330617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21886964138302567280881645 8207611551863462730330617)
        ·
          refine ⟨6155708663897597047747963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8207611551863462730330617 6155708663897597047747963)
          ·
            refine ⟨9233562995846395571621945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6155708663897597047747963 9233562995846395571621945)
            ·
              refine ⟨6925172246884796678716459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9233562995846395571621945 6925172246884796678716459)
              ·
                refine ⟨10387758370327195018074689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6925172246884796678716459 10387758370327195018074689)
                ·
                  refine ⟨7790818777745396263556017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10387758370327195018074689 7790818777745396263556017)
                  ·
                    refine ⟨5843114083309047197667013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7790818777745396263556017 5843114083309047197667013)
                    ·
                      refine ⟨1095583890620446349562565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5843114083309047197667013 1095583890620446349562565)
                      ·
                        rfl

theorem cell23_2133642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_2133642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133642 prefixEnd_2133642 := by exact prefixLift 2133642
  have htrace : WordTrace (prefixWord ++ tailWord_2133642) baseStart_2133642 baseEnd_2133642 := by
    simpa [prefixWord, tailWord_2133642, baseEnd_2133642] using wordTrace_append hprefix tailTrace_2133642
  have hstable : (prefixWord ++ tailWord_2133642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133642).length < 2 ^ (prefixWord ++ tailWord_2133642).sum := by decide
  have hdescent : baseEnd_2133642 < baseStart_2133642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133646 : List Nat := [4, 1, 1, 3, 1, 4, 1, 1, 1, 4, 2]
def baseStart_2133646 : Nat := 118140960795 + 2133646 * 2 ^ 59
def prefixEnd_2133646 : Nat := 4983230072969 + 3 ^ 40 * 2133646 * 2
def baseEnd_2133646 : Nat := 1095585944543064333912547

theorem tailTrace_2133646 : CollatzResearch.WordTrace tailWord_2133646 prefixEnd_2133646 1095585944543064333912547 := by
  unfold tailWord_2133646
  simp only [CollatzResearch.WordTrace]
  refine ⟨9727557853521551821340599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51880308552114943047149861 9727557853521551821340599)
  ·
    refine ⟨14591336780282327732010899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9727557853521551821340599 14591336780282327732010899)
    ·
      refine ⟨21887005170423491598016349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14591336780282327732010899 21887005170423491598016349)
      ·
        refine ⟨8207626938908809349256131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21887005170423491598016349 8207626938908809349256131)
        ·
          refine ⟨12311440408363214023884197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8207626938908809349256131 12311440408363214023884197)
          ·
            refine ⟨2308395076568102629478287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12311440408363214023884197 2308395076568102629478287)
            ·
              refine ⟨3462592614852153944217431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2308395076568102629478287 3462592614852153944217431)
              ·
                refine ⟨5193888922278230916326147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3462592614852153944217431 5193888922278230916326147)
                ·
                  refine ⟨7790833383417346374489221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5193888922278230916326147 7790833383417346374489221)
                  ·
                    refine ⟨1460781259390752445216729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7790833383417346374489221 1460781259390752445216729)
                    ·
                      refine ⟨1095585944543064333912547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1460781259390752445216729 1095585944543064333912547)
                      ·
                        rfl

theorem cell23_2133646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_2133646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133646 prefixEnd_2133646 := by exact prefixLift 2133646
  have htrace : WordTrace (prefixWord ++ tailWord_2133646) baseStart_2133646 baseEnd_2133646 := by
    simpa [prefixWord, tailWord_2133646, baseEnd_2133646] using wordTrace_append hprefix tailTrace_2133646
  have hstable : (prefixWord ++ tailWord_2133646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133646).length < 2 ^ (prefixWord ++ tailWord_2133646).sum := by decide
  have hdescent : baseEnd_2133646 < baseStart_2133646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133686 : List Nat := [5, 1, 3, 1, 1, 3, 1, 1, 7]
def baseStart_2133686 : Nat := 118140960795 + 2133686 * 2 ^ 59
def prefixEnd_2133686 : Nat := 4983230072969 + 3 ^ 40 * 2133686 * 2
def baseEnd_2133686 : Nat := 121734053752138241934707

theorem tailTrace_2133686 : CollatzResearch.WordTrace tailWord_2133686 prefixEnd_2133686 121734053752138241934707 := by
  unfold tailWord_2133686
  simp only [CollatzResearch.WordTrace]
  refine ⟨4863870109251718837636307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51881281165351667601453941 4863870109251718837636307)
  ·
    refine ⟨7295805163877578256454461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4863870109251718837636307 7295805163877578256454461)
    ·
      refine ⟨2735926936454091846170423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7295805163877578256454461 2735926936454091846170423)
      ·
        refine ⟨4103890404681137769255635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2735926936454091846170423 4103890404681137769255635)
        ·
          refine ⟨6155835607021706653883453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4103890404681137769255635 6155835607021706653883453)
          ·
            refine ⟨2308438352633139995206295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6155835607021706653883453 2308438352633139995206295)
            ·
              refine ⟨3462657528949709992809443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2308438352633139995206295 3462657528949709992809443)
              ·
                refine ⟨5193986293424564989214165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3462657528949709992809443 5193986293424564989214165)
                ·
                  refine ⟨121734053752138241934707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5193986293424564989214165 121734053752138241934707)
                  ·
                    rfl

theorem cell23_2133686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_2133686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133686 prefixEnd_2133686 := by exact prefixLift 2133686
  have htrace : WordTrace (prefixWord ++ tailWord_2133686) baseStart_2133686 baseEnd_2133686 := by
    simpa [prefixWord, tailWord_2133686, baseEnd_2133686] using wordTrace_append hprefix tailTrace_2133686
  have hstable : (prefixWord ++ tailWord_2133686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133686).length < 2 ^ (prefixWord ++ tailWord_2133686).sum := by decide
  have hdescent : baseEnd_2133686 < baseStart_2133686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133692 : List Nat := [2, 2, 2, 3, 1, 3, 1, 1, 1, 2, 5]
def baseStart_2133692 : Nat := 118140960795 + 2133692 * 2 ^ 59
def prefixEnd_2133692 : Nat := 4983230072969 + 3 ^ 40 * 2133692 * 2
def baseEnd_2133692 : Nat := 1095609564653171153937335

theorem tailTrace_2133692 : CollatzResearch.WordTrace tailWord_2133692 prefixEnd_2133692 1095609564653171153937335 := by
  unfold tailWord_2133692
  simp only [CollatzResearch.WordTrace]
  refine ⟨38911070293002882213449665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51881427057337176284599553 38911070293002882213449665)
  ·
    refine ⟨29183302719752161660087249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38911070293002882213449665 29183302719752161660087249)
    ·
      refine ⟨21887477039814121245065437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29183302719752161660087249 21887477039814121245065437)
      ·
        refine ⟨8207803889930295466899539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21887477039814121245065437 8207803889930295466899539)
        ·
          refine ⟨12311705834895443200349309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8207803889930295466899539 12311705834895443200349309)
          ·
            refine ⟨4616889688085791200130991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12311705834895443200349309 4616889688085791200130991)
            ·
              refine ⟨6925334532128686800196487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4616889688085791200130991 6925334532128686800196487)
              ·
                refine ⟨10388001798193030200294731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6925334532128686800196487 10388001798193030200294731)
                ·
                  refine ⟨15582002697289545300442097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10388001798193030200294731 15582002697289545300442097)
                  ·
                    refine ⟨11686502022967158975331573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15582002697289545300442097 11686502022967158975331573)
                    ·
                      refine ⟨1095609564653171153937335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11686502022967158975331573 1095609564653171153937335)
                      ·
                        rfl

theorem cell23_2133692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_2133692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133692 prefixEnd_2133692 := by exact prefixLift 2133692
  have htrace : WordTrace (prefixWord ++ tailWord_2133692) baseStart_2133692 baseEnd_2133692 := by
    simpa [prefixWord, tailWord_2133692, baseEnd_2133692] using wordTrace_append hprefix tailTrace_2133692
  have hstable : (prefixWord ++ tailWord_2133692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133692).length < 2 ^ (prefixWord ++ tailWord_2133692).sum := by decide
  have hdescent : baseEnd_2133692 < baseStart_2133692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133746 : List Nat := [3, 2, 1, 3, 1, 1, 3, 4, 1, 4]
def baseStart_2133746 : Nat := 118140960795 + 2133746 * 2 ^ 59
def prefixEnd_2133746 : Nat := 4983230072969 + 3 ^ 40 * 2133746 * 2
def baseEnd_2133746 : Nat := 365212430869504647554029

theorem tailTrace_2133746 : CollatzResearch.WordTrace tailWord_2133746 prefixEnd_2133746 365212430869504647554029 := by
  unfold tailWord_2133746
  simp only [CollatzResearch.WordTrace]
  refine ⟨19456027531952532912341273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51882740085206754432910061 19456027531952532912341273)
  ·
    refine ⟨14592020648964399684255955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19456027531952532912341273 14592020648964399684255955)
    ·
      refine ⟨21888030973446599526383933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14592020648964399684255955 21888030973446599526383933)
      ·
        refine ⟨8208011615042474822393975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21888030973446599526383933 8208011615042474822393975)
        ·
          refine ⟨12312017422563712233590963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8208011615042474822393975 12312017422563712233590963)
          ·
            refine ⟨18468026133845568350386445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12312017422563712233590963 18468026133845568350386445)
            ·
              refine ⟨6925509800192088131394917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18468026133845568350386445 6925509800192088131394917)
              ·
                refine ⟨1298533087536016524636547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6925509800192088131394917 1298533087536016524636547)
                ·
                  refine ⟨1947799631304024786954821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1298533087536016524636547 1947799631304024786954821)
                  ·
                    refine ⟨365212430869504647554029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1947799631304024786954821 365212430869504647554029)
                    ·
                      rfl

theorem cell23_2133746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 4, 1, 4].length) (baseStart_2133746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133746 prefixEnd_2133746 := by exact prefixLift 2133746
  have htrace : WordTrace (prefixWord ++ tailWord_2133746) baseStart_2133746 baseEnd_2133746 := by
    simpa [prefixWord, tailWord_2133746, baseEnd_2133746] using wordTrace_append hprefix tailTrace_2133746
  have hstable : (prefixWord ++ tailWord_2133746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133746).length < 2 ^ (prefixWord ++ tailWord_2133746).sum := by decide
  have hdescent : baseEnd_2133746 < baseStart_2133746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133772 : List Nat := [2, 2, 1, 2, 2, 1, 4, 1, 3, 5]
def baseStart_2133772 : Nat := 118140960795 + 2133772 * 2 ^ 59
def prefixEnd_2133772 : Nat := 4983230072969 + 3 ^ 40 * 2133772 * 2
def baseEnd_2133772 : Nat := 365216881035176946978989

theorem tailTrace_2133772 : CollatzResearch.WordTrace tailWord_2133772 prefixEnd_2133772 365216881035176946978989 := by
  unfold tailWord_2133772
  simp only [CollatzResearch.WordTrace]
  refine ⟨38912529212857969044905785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51883372283810625393207713 38912529212857969044905785)
  ·
    refine ⟨29184396909643476783679339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38912529212857969044905785 29184396909643476783679339)
    ·
      refine ⟨43776595364465215175519009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29184396909643476783679339 43776595364465215175519009)
      ·
        refine ⟨32832446523348911381639257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43776595364465215175519009 32832446523348911381639257)
        ·
          refine ⟨24624334892511683536229443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32832446523348911381639257 24624334892511683536229443)
          ·
            refine ⟨36936502338767525304344165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24624334892511683536229443 36936502338767525304344165)
            ·
              refine ⟨6925594188518910994564531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36936502338767525304344165 6925594188518910994564531)
              ·
                refine ⟨10388391282778366491846797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6925594188518910994564531 10388391282778366491846797)
                ·
                  refine ⟨3895646731041887434442549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10388391282778366491846797 3895646731041887434442549)
                  ·
                    refine ⟨365216881035176946978989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3895646731041887434442549 365216881035176946978989)
                    ·
                      rfl

theorem cell23_2133772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 3, 5].length) (baseStart_2133772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133772 prefixEnd_2133772 := by exact prefixLift 2133772
  have htrace : WordTrace (prefixWord ++ tailWord_2133772) baseStart_2133772 baseEnd_2133772 := by
    simpa [prefixWord, tailWord_2133772, baseEnd_2133772] using wordTrace_append hprefix tailTrace_2133772
  have hstable : (prefixWord ++ tailWord_2133772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133772).length < 2 ^ (prefixWord ++ tailWord_2133772).sum := by decide
  have hdescent : baseEnd_2133772 < baseStart_2133772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133779 : List Nat := [1, 1, 1, 2, 1, 3, 2, 5, 2, 3, 2]
def baseStart_2133779 : Nat := 118140960795 + 2133779 * 2 ^ 59
def prefixEnd_2133779 : Nat := 4983230072969 + 3 ^ 40 * 2133779 * 2
def baseEnd_2133779 : Nat := 1095654237470112313549435

theorem tailTrace_2133779 : CollatzResearch.WordTrace tailWord_2133779 prefixEnd_2133779 1095654237470112313549435 := by
  unfold tailWord_2133779
  simp only [CollatzResearch.WordTrace]
  refine ⟨77825313736690578285316391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51883542491127052190210927 77825313736690578285316391)
  ·
    refine ⟨116737970605035867427974587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77825313736690578285316391 116737970605035867427974587)
    ·
      refine ⟨175106955907553801141961881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116737970605035867427974587 175106955907553801141961881)
      ·
        refine ⟨131330216930665350856471411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175106955907553801141961881 131330216930665350856471411)
        ·
          refine ⟨196995325395998026284707117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131330216930665350856471411 196995325395998026284707117)
          ·
            refine ⟨73873247023499259856765169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 196995325395998026284707117 73873247023499259856765169)
            ·
              refine ⟨55404935267624444892573877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73873247023499259856765169 55404935267624444892573877)
              ·
                refine ⟨5194212681339791708678801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55404935267624444892573877 5194212681339791708678801)
                ·
                  refine ⟨3895659511004843781509101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5194212681339791708678801 3895659511004843781509101)
                  ·
                    refine ⟨1460872316626816418065913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3895659511004843781509101 1460872316626816418065913)
                    ·
                      refine ⟨1095654237470112313549435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1460872316626816418065913 1095654237470112313549435)
                      ·
                        rfl

theorem cell23_2133779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 2, 3, 2].length) (baseStart_2133779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133779 prefixEnd_2133779 := by exact prefixLift 2133779
  have htrace : WordTrace (prefixWord ++ tailWord_2133779) baseStart_2133779 baseEnd_2133779 := by
    simpa [prefixWord, tailWord_2133779, baseEnd_2133779] using wordTrace_append hprefix tailTrace_2133779
  have hstable : (prefixWord ++ tailWord_2133779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133779).length < 2 ^ (prefixWord ++ tailWord_2133779).sum := by decide
  have hdescent : baseEnd_2133779 < baseStart_2133779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133785 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 2, 10]
def baseStart_2133785 : Nat := 118140960795 + 2133785 * 2 ^ 59
def prefixEnd_2133785 : Nat := 4983230072969 + 3 ^ 40 * 2133785 * 2
def baseEnd_2133785 : Nat := 365219106118013096691469

theorem tailTrace_2133785 : CollatzResearch.WordTrace tailWord_2133785 prefixEnd_2133785 365219106118013096691469 := by
  unfold tailWord_2133785
  simp only [CollatzResearch.WordTrace]
  refine ⟨77825532574668841310034809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51883688383112560873356539 77825532574668841310034809)
  ·
    refine ⟨58369149431001630982526107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77825532574668841310034809 58369149431001630982526107)
    ·
      refine ⟨87553724146502446473789161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58369149431001630982526107 87553724146502446473789161)
      ·
        refine ⟨65665293109876834855341871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87553724146502446473789161 65665293109876834855341871)
        ·
          refine ⟨98497939664815252283012807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65665293109876834855341871 98497939664815252283012807)
          ·
            refine ⟨147746909497222878424519211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98497939664815252283012807 147746909497222878424519211)
            ·
              refine ⟨221620364245834317636778817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147746909497222878424519211 221620364245834317636778817)
              ·
                refine ⟨166215273184375738227584113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 221620364245834317636778817 166215273184375738227584113)
                ·
                  refine ⟨124661454888281803670688085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 166215273184375738227584113 124661454888281803670688085)
                  ·
                    refine ⟨365219106118013096691469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 124661454888281803670688085 365219106118013096691469)
                    ·
                      rfl

theorem cell23_2133785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 10].length) (baseStart_2133785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133785 prefixEnd_2133785 := by exact prefixLift 2133785
  have htrace : WordTrace (prefixWord ++ tailWord_2133785) baseStart_2133785 baseEnd_2133785 := by
    simpa [prefixWord, tailWord_2133785, baseEnd_2133785] using wordTrace_append hprefix tailTrace_2133785
  have hstable : (prefixWord ++ tailWord_2133785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133785).length < 2 ^ (prefixWord ++ tailWord_2133785).sum := by decide
  have hdescent : baseEnd_2133785 < baseStart_2133785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133832 : List Nat := [2, 1, 3, 1, 1, 5, 1, 9]
def baseStart_2133832 : Nat := 118140960795 + 2133832 * 2 ^ 59
def prefixEnd_2133832 : Nat := 4983230072969 + 3 ^ 40 * 2133832 * 2
def baseEnd_2133832 : Nat := 40580794516474096525433

theorem tailTrace_2133832 : CollatzResearch.WordTrace tailWord_2133832 prefixEnd_2133832 40580794516474096525433 := by
  unfold tailWord_2133832
  simp only [CollatzResearch.WordTrace]
  refine ⟨38913623402749284168497875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51884831203665712224663833 38913623402749284168497875)
  ·
    refine ⟨58370435104123926252746813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38913623402749284168497875 58370435104123926252746813)
    ·
      refine ⟨21888913164046472344780055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58370435104123926252746813 21888913164046472344780055)
      ·
        refine ⟨32833369746069708517170083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21888913164046472344780055 32833369746069708517170083)
        ·
          refine ⟨49250054619104562775755125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32833369746069708517170083 49250054619104562775755125)
          ·
            refine ⟨4617192620541052760227043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49250054619104562775755125 4617192620541052760227043)
            ·
              refine ⟨6925788930811579140340565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4617192620541052760227043 6925788930811579140340565)
              ·
                refine ⟨40580794516474096525433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6925788930811579140340565 40580794516474096525433)
                ·
                  rfl

theorem cell23_2133832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 9].length) (baseStart_2133832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133832 prefixEnd_2133832 := by exact prefixLift 2133832
  have htrace : WordTrace (prefixWord ++ tailWord_2133832) baseStart_2133832 baseEnd_2133832 := by
    simpa [prefixWord, tailWord_2133832, baseEnd_2133832] using wordTrace_append hprefix tailTrace_2133832
  have hstable : (prefixWord ++ tailWord_2133832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133832).length < 2 ^ (prefixWord ++ tailWord_2133832).sum := by decide
  have hdescent : baseEnd_2133832 < baseStart_2133832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133837 : List Nat := [1, 6, 1, 2, 1, 3, 1, 3, 1, 1, 3]
def baseStart_2133837 : Nat := 118140960795 + 2133837 * 2 ^ 59
def prefixEnd_2133837 : Nat := 4983230072969 + 3 ^ 40 * 2133837 * 2
def baseEnd_2133837 : Nat := 1095684019348073086624169

theorem tailTrace_2133837 : CollatzResearch.WordTrace tailWord_2133837 prefixEnd_2133837 1095684019348073086624169 := by
  unfold tailWord_2133837
  simp only [CollatzResearch.WordTrace]
  refine ⟨77827429170480454190927765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51884952780320302793951843 77827429170480454190927765)
  ·
    refine ⟨3648160742366271290199739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 77827429170480454190927765 3648160742366271290199739)
    ·
      refine ⟨5472241113549406935299609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3648160742366271290199739 5472241113549406935299609)
      ·
        refine ⟨4104180835162055201474707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5472241113549406935299609 4104180835162055201474707)
        ·
          refine ⟨6156271252743082802212061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4104180835162055201474707 6156271252743082802212061)
          ·
            refine ⟨2308601719778656050829523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6156271252743082802212061 2308601719778656050829523)
            ·
              refine ⟨3462902579667984076244285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2308601719778656050829523 3462902579667984076244285)
              ·
                refine ⟨1298588467375494028591607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3462902579667984076244285 1298588467375494028591607)
                ·
                  refine ⟨1947882701063241042887411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1298588467375494028591607 1947882701063241042887411)
                  ·
                    refine ⟨2921824051594861564331117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1947882701063241042887411 2921824051594861564331117)
                    ·
                      refine ⟨1095684019348073086624169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2921824051594861564331117 1095684019348073086624169)
                      ·
                        rfl

theorem cell23_2133837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_2133837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133837 prefixEnd_2133837 := by exact prefixLift 2133837
  have htrace : WordTrace (prefixWord ++ tailWord_2133837) baseStart_2133837 baseEnd_2133837 := by
    simpa [prefixWord, tailWord_2133837, baseEnd_2133837] using wordTrace_append hprefix tailTrace_2133837
  have hstable : (prefixWord ++ tailWord_2133837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133837).length < 2 ^ (prefixWord ++ tailWord_2133837).sum := by decide
  have hdescent : baseEnd_2133837 < baseStart_2133837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133860 : List Nat := [2, 3, 1, 1, 5, 2, 1, 1, 3, 2, 2]
def baseStart_2133860 : Nat := 118140960795 + 2133860 * 2 ^ 59
def prefixEnd_2133860 : Nat := 4983230072969 + 3 ^ 40 * 2133860 * 2
def baseEnd_2133860 : Nat := 1095695829403126496636563

theorem tailTrace_2133860 : CollatzResearch.WordTrace tailWord_2133860 prefixEnd_2133860 1095695829403126496636563 := by
  unfold tailWord_2133860
  simp only [CollatzResearch.WordTrace]
  refine ⟨38914134024698564559507517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51885512032931419412676689 38914134024698564559507517)
  ·
    refine ⟨14592800259261961709815319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38914134024698564559507517 14592800259261961709815319)
    ·
      refine ⟨21889200388892942564722979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14592800259261961709815319 21889200388892942564722979)
      ·
        refine ⟨32833800583339413847084469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21889200388892942564722979 32833800583339413847084469)
        ·
          refine ⟨3078168804688070048164169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32833800583339413847084469 3078168804688070048164169)
          ·
            refine ⟨2308626603516052536123127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3078168804688070048164169 2308626603516052536123127)
            ·
              refine ⟨3462939905274078804184691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2308626603516052536123127 3462939905274078804184691)
              ·
                refine ⟨5194409857911118206277037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3462939905274078804184691 5194409857911118206277037)
                ·
                  refine ⟨1947903696716669327353889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5194409857911118206277037 1947903696716669327353889)
                  ·
                    refine ⟨1460927772537501995515417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1947903696716669327353889 1460927772537501995515417)
                    ·
                      refine ⟨1095695829403126496636563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1460927772537501995515417 1095695829403126496636563)
                      ·
                        rfl

theorem cell23_2133860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 3, 2, 2].length) (baseStart_2133860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133860 prefixEnd_2133860 := by exact prefixLift 2133860
  have htrace : WordTrace (prefixWord ++ tailWord_2133860) baseStart_2133860 baseEnd_2133860 := by
    simpa [prefixWord, tailWord_2133860, baseEnd_2133860] using wordTrace_append hprefix tailTrace_2133860
  have hstable : (prefixWord ++ tailWord_2133860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133860).length < 2 ^ (prefixWord ++ tailWord_2133860).sum := by decide
  have hdescent : baseEnd_2133860 < baseStart_2133860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133866 : List Nat := [3, 1, 3, 4, 1, 1, 2, 8]
def baseStart_2133866 : Nat := 118140960795 + 2133866 * 2 ^ 59
def prefixEnd_2133866 : Nat := 4983230072969 + 3 ^ 40 * 2133866 * 2
def baseEnd_2133866 : Nat := 40581441121742721228205

theorem tailTrace_2133866 : CollatzResearch.WordTrace tailWord_2133866 prefixEnd_2133866 40581441121742721228205 := by
  unfold tailWord_2133866
  simp only [CollatzResearch.WordTrace]
  refine ⟨19457121721843848035933363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51885657924916928095822301 19457121721843848035933363)
  ·
    refine ⟨29185682582765772053900045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19457121721843848035933363 29185682582765772053900045)
    ·
      refine ⟨10944630968537164520212517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29185682582765772053900045 10944630968537164520212517)
      ·
        refine ⟨2052118306600718347539847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10944630968537164520212517 2052118306600718347539847)
        ·
          refine ⟨3078177459901077521309771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2052118306600718347539847 3078177459901077521309771)
          ·
            refine ⟨4617266189851616281964657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3078177459901077521309771 4617266189851616281964657)
            ·
              refine ⟨3462949642388712211473493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4617266189851616281964657 3462949642388712211473493)
              ·
                refine ⟨40581441121742721228205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3462949642388712211473493 40581441121742721228205)
                ·
                  rfl

theorem cell23_2133866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 8].length) (baseStart_2133866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133866 prefixEnd_2133866 := by exact prefixLift 2133866
  have htrace : WordTrace (prefixWord ++ tailWord_2133866) baseStart_2133866 baseEnd_2133866 := by
    simpa [prefixWord, tailWord_2133866, baseEnd_2133866] using wordTrace_append hprefix tailTrace_2133866
  have hstable : (prefixWord ++ tailWord_2133866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133866).length < 2 ^ (prefixWord ++ tailWord_2133866).sum := by decide
  have hdescent : baseEnd_2133866 < baseStart_2133866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133870 : List Nat := [4, 1, 2, 3, 1, 3, 2, 1, 2, 4]
def baseStart_2133870 : Nat := 118140960795 + 2133870 * 2 ^ 59
def prefixEnd_2133870 : Nat := 4983230072969 + 3 ^ 40 * 2133870 * 2
def baseEnd_2133870 : Nat := 365233654736557152503839

theorem tailTrace_2133870 : CollatzResearch.WordTrace tailWord_2133870 prefixEnd_2133870 365233654736557152503839 := by
  unfold tailWord_2133870
  simp only [CollatzResearch.WordTrace]
  refine ⟨9728579097420112603359883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51885755186240600551252709 9728579097420112603359883)
  ·
    refine ⟨14592868646130168905039825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9728579097420112603359883 14592868646130168905039825)
    ·
      refine ⟨10944651484597626678779869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14592868646130168905039825 10944651484597626678779869)
      ·
        refine ⟨4104244306724110004542451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10944651484597626678779869 4104244306724110004542451)
        ·
          refine ⟨6156366460086165006813677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4104244306724110004542451 6156366460086165006813677)
          ·
            refine ⟨2308637422532311877555129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6156366460086165006813677 2308637422532311877555129)
            ·
              refine ⟨1731478066899233908166347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2308637422532311877555129 1731478066899233908166347)
              ·
                refine ⟨2597217100348850862249521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1731478066899233908166347 2597217100348850862249521)
                ·
                  refine ⟨1947912825261638146687141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2597217100348850862249521 1947912825261638146687141)
                  ·
                    refine ⟨365233654736557152503839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1947912825261638146687141 365233654736557152503839)
                    ·
                      rfl

theorem cell23_2133870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_2133870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133870 prefixEnd_2133870 := by exact prefixLift 2133870
  have htrace : WordTrace (prefixWord ++ tailWord_2133870) baseStart_2133870 baseEnd_2133870 := by
    simpa [prefixWord, tailWord_2133870, baseEnd_2133870] using wordTrace_append hprefix tailTrace_2133870
  have hstable : (prefixWord ++ tailWord_2133870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133870).length < 2 ^ (prefixWord ++ tailWord_2133870).sum := by decide
  have hdescent : baseEnd_2133870 < baseStart_2133870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134089 : List Nat := [1, 2, 1, 1, 2, 2, 3, 2, 3, 6]
def baseStart_2134089 : Nat := 118140960795 + 2134089 * 2 ^ 59
def prefixEnd_2134089 : Nat := 4983230072969 + 3 ^ 40 * 2134089 * 2
def baseEnd_2134089 : Nat := 365271138824335366891003

theorem tailTrace_2134089 : CollatzResearch.WordTrace tailWord_2134089 prefixEnd_2134089 365271138824335366891003 := by
  unfold tailWord_2134089
  simp only [CollatzResearch.WordTrace]
  refine ⟨77836620365567501229101321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51891080243711667486067547 77836620365567501229101321)
  ·
    refine ⟨58377465274175625921825991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77836620365567501229101321 58377465274175625921825991)
    ·
      refine ⟨87566197911263438882738987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58377465274175625921825991 87566197911263438882738987)
      ·
        refine ⟨131349296866895158324108481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87566197911263438882738987 131349296866895158324108481)
        ·
          refine ⟨98511972650171368743081361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131349296866895158324108481 98511972650171368743081361)
          ·
            refine ⟨73883979487628526557311021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98511972650171368743081361 73883979487628526557311021)
            ·
              refine ⟨27706492307860697458991633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73883979487628526557311021 27706492307860697458991633)
              ·
                refine ⟨20779869230895523094243725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27706492307860697458991633 20779869230895523094243725)
                ·
                  refine ⟨7792450961585821160341397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20779869230895523094243725 7792450961585821160341397)
                  ·
                    refine ⟨365271138824335366891003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7792450961585821160341397 365271138824335366891003)
                    ·
                      rfl

theorem cell23_2134089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 6].length) (baseStart_2134089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134089 prefixEnd_2134089 := by exact prefixLift 2134089
  have htrace : WordTrace (prefixWord ++ tailWord_2134089) baseStart_2134089 baseEnd_2134089 := by
    simpa [prefixWord, tailWord_2134089, baseEnd_2134089] using wordTrace_append hprefix tailTrace_2134089
  have hstable : (prefixWord ++ tailWord_2134089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134089).length < 2 ^ (prefixWord ++ tailWord_2134089).sum := by decide
  have hdescent : baseEnd_2134089 < baseStart_2134089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134096 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 4, 6, 2]
def baseStart_2134096 : Nat := 118140960795 + 2134096 * 2 ^ 59
def prefixEnd_2134096 : Nat := 4983230072969 + 3 ^ 40 * 2134096 * 2
def baseEnd_2134096 : Nat := 1095817010837587573285477

theorem tailTrace_2134096 : CollatzResearch.WordTrace tailWord_2134096 prefixEnd_2134096 1095817010837587573285477 := by
  unfold tailWord_2134096
  simp only [CollatzResearch.WordTrace]
  refine ⟨38918437838271070712303071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51891250451028094283070761 38918437838271070712303071)
  ·
    refine ⟨58377656757406606068454607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38918437838271070712303071 58377656757406606068454607)
    ·
      refine ⟨87566485136109909102681911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58377656757406606068454607 87566485136109909102681911)
      ·
        refine ⟨131349727704164863654022867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87566485136109909102681911 131349727704164863654022867)
        ·
          refine ⟨197024591556247295481034301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131349727704164863654022867 197024591556247295481034301)
          ·
            refine ⟨73884221833592735805387863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 197024591556247295481034301 73884221833592735805387863)
            ·
              refine ⟨110826332750389103708081795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73884221833592735805387863 110826332750389103708081795)
              ·
                refine ⟨166239499125583655562122693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110826332750389103708081795 166239499125583655562122693)
                ·
                  refine ⟨31169906086046935417898005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 166239499125583655562122693 31169906086046935417898005)
                  ·
                    refine ⟨1461089347783450097713969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 31169906086046935417898005 1461089347783450097713969)
                    ·
                      refine ⟨1095817010837587573285477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1461089347783450097713969 1095817010837587573285477)
                      ·
                        rfl

theorem cell23_2134096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 4, 6, 2].length) (baseStart_2134096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134096 prefixEnd_2134096 := by exact prefixLift 2134096
  have htrace : WordTrace (prefixWord ++ tailWord_2134096) baseStart_2134096 baseEnd_2134096 := by
    simpa [prefixWord, tailWord_2134096, baseEnd_2134096] using wordTrace_append hprefix tailTrace_2134096
  have hstable : (prefixWord ++ tailWord_2134096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134096).length < 2 ^ (prefixWord ++ tailWord_2134096).sum := by decide
  have hdescent : baseEnd_2134096 < baseStart_2134096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134106 : List Nat := [3, 1, 1, 2, 1, 1, 6, 1, 1, 6]
def baseStart_2134106 : Nat := 118140960795 + 2134106 * 2 ^ 59
def prefixEnd_2134106 : Nat := 4983230072969 + 3 ^ 40 * 2134106 * 2
def baseEnd_2134106 : Nat := 365274048548044178053477

theorem tailTrace_2134106 : CollatzResearch.WordTrace tailWord_2134106 prefixEnd_2134106 365274048548044178053477 := by
  unfold tailWord_2134106
  simp only [CollatzResearch.WordTrace]
  refine ⟨19459310101626478283117543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51891493604337275421646781 19459310101626478283117543)
  ·
    refine ⟨29188965152439717424676315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19459310101626478283117543 29188965152439717424676315)
    ·
      refine ⟨43783447728659576137014473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29188965152439717424676315 43783447728659576137014473)
      ·
        refine ⟨32837585796494682102760855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43783447728659576137014473 32837585796494682102760855)
        ·
          refine ⟨49256378694742023154141283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32837585796494682102760855 49256378694742023154141283)
          ·
            refine ⟨73884568042113034731211925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49256378694742023154141283 73884568042113034731211925)
            ·
              refine ⟨3463339126974048503025559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 73884568042113034731211925 3463339126974048503025559)
              ·
                refine ⟨5195008690461072754538339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3463339126974048503025559 5195008690461072754538339)
                ·
                  refine ⟨7792513035691609131807509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5195008690461072754538339 7792513035691609131807509)
                  ·
                    refine ⟨365274048548044178053477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7792513035691609131807509 365274048548044178053477)
                    ·
                      rfl

theorem cell23_2134106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 1, 6].length) (baseStart_2134106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134106 prefixEnd_2134106 := by exact prefixLift 2134106
  have htrace : WordTrace (prefixWord ++ tailWord_2134106) baseStart_2134106 baseEnd_2134106 := by
    simpa [prefixWord, tailWord_2134106, baseEnd_2134106] using wordTrace_append hprefix tailTrace_2134106
  have hstable : (prefixWord ++ tailWord_2134106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134106).length < 2 ^ (prefixWord ++ tailWord_2134106).sum := by decide
  have hdescent : baseEnd_2134106 < baseStart_2134106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134130 : List Nat := [3, 2, 1, 2, 2, 2, 4, 1, 1, 1, 4]
def baseStart_2134130 : Nat := 118140960795 + 2134130 * 2 ^ 59
def prefixEnd_2134130 : Nat := 4983230072969 + 3 ^ 40 * 2134130 * 2
def baseEnd_2134130 : Nat := 1095834469179840440260321

theorem tailTrace_2134130 : CollatzResearch.WordTrace tailWord_2134130 prefixEnd_2134130 1095834469179840440260321 := by
  unfold tailWord_2134130
  simp only [CollatzResearch.WordTrace]
  refine ⟨19459528939604741307835961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51892077172279310154229229 19459528939604741307835961)
  ·
    refine ⟨14594646704703555980876971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19459528939604741307835961 14594646704703555980876971)
    ·
      refine ⟨21891970057055333971315457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14594646704703555980876971 21891970057055333971315457)
      ·
        refine ⟨16418977542791500478486593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21891970057055333971315457 16418977542791500478486593)
        ·
          refine ⟨12314233157093625358864945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16418977542791500478486593 12314233157093625358864945)
          ·
            refine ⟨9235674867820219019148709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12314233157093625358864945 9235674867820219019148709)
            ·
              refine ⟨1731689037716291066090383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9235674867820219019148709 1731689037716291066090383)
              ·
                refine ⟨2597533556574436599135575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1731689037716291066090383 2597533556574436599135575)
                ·
                  refine ⟨3896300334861654898703363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2597533556574436599135575 3896300334861654898703363)
                  ·
                    refine ⟨5844450502292482348055045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3896300334861654898703363 5844450502292482348055045)
                    ·
                      refine ⟨1095834469179840440260321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5844450502292482348055045 1095834469179840440260321)
                      ·
                        rfl

theorem cell23_2134130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 1, 1, 1, 4].length) (baseStart_2134130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134130 prefixEnd_2134130 := by exact prefixLift 2134130
  have htrace : WordTrace (prefixWord ++ tailWord_2134130) baseStart_2134130 baseEnd_2134130 := by
    simpa [prefixWord, tailWord_2134130, baseEnd_2134130] using wordTrace_append hprefix tailTrace_2134130
  have hstable : (prefixWord ++ tailWord_2134130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134130).length < 2 ^ (prefixWord ++ tailWord_2134130).sum := by decide
  have hdescent : baseEnd_2134130 < baseStart_2134130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134139 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 6]
def baseStart_2134139 : Nat := 118140960795 + 2134139 * 2 ^ 59
def prefixEnd_2134139 : Nat := 4983230072969 + 3 ^ 40 * 2134139 * 2
def baseEnd_2134139 : Nat := 1095839090505730905047779

theorem tailTrace_2134139 : CollatzResearch.WordTrace tailWord_2134139 prefixEnd_2134139 1095839090505730905047779 := by
  unfold tailWord_2134139
  simp only [CollatzResearch.WordTrace]
  refine ⟨77838444015386359768421471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51892296010257573178947647 77838444015386359768421471)
  ·
    refine ⟨116757666023079539652632207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77838444015386359768421471 116757666023079539652632207)
    ·
      refine ⟨175136499034619309478948311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116757666023079539652632207 175136499034619309478948311)
      ·
        refine ⟨262704748551928964218422467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175136499034619309478948311 262704748551928964218422467)
        ·
          refine ⟨394057122827893446327633701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262704748551928964218422467 394057122827893446327633701)
          ·
            refine ⟨73885710530230021186431319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 394057122827893446327633701 73885710530230021186431319)
            ·
              refine ⟨110828565795345031779646979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73885710530230021186431319 110828565795345031779646979)
              ·
                refine ⟨166242848693017547669470469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110828565795345031779646979 166242848693017547669470469)
                ·
                  refine ⟨31170534129940790188025713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 166242848693017547669470469 31170534129940790188025713)
                  ·
                    refine ⟨23377900597455592641019285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31170534129940790188025713 23377900597455592641019285)
                    ·
                      refine ⟨1095839090505730905047779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23377900597455592641019285 1095839090505730905047779)
                      ·
                        rfl

theorem cell23_2134139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 6].length) (baseStart_2134139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134139 prefixEnd_2134139 := by exact prefixLift 2134139
  have htrace : WordTrace (prefixWord ++ tailWord_2134139) baseStart_2134139 baseEnd_2134139 := by
    simpa [prefixWord, tailWord_2134139, baseEnd_2134139] using wordTrace_append hprefix tailTrace_2134139
  have hstable : (prefixWord ++ tailWord_2134139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134139).length < 2 ^ (prefixWord ++ tailWord_2134139).sum := by decide
  have hdescent : baseEnd_2134139 < baseStart_2134139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134140 : List Nat := [2, 2, 2, 1, 1, 6, 1, 2, 2, 4]
def baseStart_2134140 : Nat := 118140960795 + 2134140 * 2 ^ 59
def prefixEnd_2134140 : Nat := 4983230072969 + 3 ^ 40 * 2134140 * 2
def baseEnd_2134140 : Nat := 365279867995461800378425

theorem tailTrace_2134140 : CollatzResearch.WordTrace tailWord_2134140 prefixEnd_2134140 365279867995461800378425 := by
  unfold tailWord_2134140
  simp only [CollatzResearch.WordTrace]
  refine ⟨38919240244191368469603937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51892320325588491292805249 38919240244191368469603937)
  ·
    refine ⟨29189430183143526352202953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38919240244191368469603937 29189430183143526352202953)
    ·
      refine ⟨21892072637357644764152215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29189430183143526352202953 21892072637357644764152215)
      ·
        refine ⟨32838108956036467146228323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21892072637357644764152215 32838108956036467146228323)
        ·
          refine ⟨49257163434054700719342485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32838108956036467146228323 49257163434054700719342485)
          ·
            refine ⟨2308929535971314096219179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 49257163434054700719342485 2308929535971314096219179)
            ·
              refine ⟨3463394303956971144328769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2308929535971314096219179 3463394303956971144328769)
              ·
                refine ⟨2597545727967728358246577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3463394303956971144328769 2597545727967728358246577)
                ·
                  refine ⟨1948159295975796268684933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2597545727967728358246577 1948159295975796268684933)
                  ·
                    refine ⟨365279867995461800378425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1948159295975796268684933 365279867995461800378425)
                    ·
                      rfl

theorem cell23_2134140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 2, 2, 4].length) (baseStart_2134140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134140 prefixEnd_2134140 := by exact prefixLift 2134140
  have htrace : WordTrace (prefixWord ++ tailWord_2134140) baseStart_2134140 baseEnd_2134140 := by
    simpa [prefixWord, tailWord_2134140, baseEnd_2134140] using wordTrace_append hprefix tailTrace_2134140
  have hstable : (prefixWord ++ tailWord_2134140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134140).length < 2 ^ (prefixWord ++ tailWord_2134140).sum := by decide
  have hdescent : baseEnd_2134140 < baseStart_2134140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134147 : List Nat := [1, 1, 1, 3, 3, 3, 2, 4, 1, 2, 2]
def baseStart_2134147 : Nat := 118140960795 + 2134147 * 2 ^ 59
def prefixEnd_2134147 : Nat := 4983230072969 + 3 ^ 40 * 2134147 * 2
def baseEnd_2134147 : Nat := 1095843198350966873747743

theorem tailTrace_2134147 : CollatzResearch.WordTrace tailWord_2134147 prefixEnd_2134147 1095843198350966873747743 := by
  unfold tailWord_2134147
  simp only [CollatzResearch.WordTrace]
  refine ⟨77838735799357377134712695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51892490532904918089808463 77838735799357377134712695)
  ·
    refine ⟨116758103699036065702069043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77838735799357377134712695 116758103699036065702069043)
    ·
      refine ⟨175137155548554098553103565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116758103699036065702069043 175137155548554098553103565)
      ·
        refine ⟨65676433330707786957413837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175137155548554098553103565 65676433330707786957413837)
        ·
          refine ⟨24628662499015420109030189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65676433330707786957413837 24628662499015420109030189)
          ·
            refine ⟨9235748437130782540886321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24628662499015420109030189 9235748437130782540886321)
            ·
              refine ⟨6926811327848086905664741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9235748437130782540886321 6926811327848086905664741)
              ·
                refine ⟨1298777123971516294812139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6926811327848086905664741 1298777123971516294812139)
                ·
                  refine ⟨1948165685957274442218209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1298777123971516294812139 1948165685957274442218209)
                  ·
                    refine ⟨1461124264467955831663657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1948165685957274442218209 1461124264467955831663657)
                    ·
                      refine ⟨1095843198350966873747743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1461124264467955831663657 1095843198350966873747743)
                      ·
                        rfl

theorem cell23_2134147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 4, 1, 2, 2].length) (baseStart_2134147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134147 prefixEnd_2134147 := by exact prefixLift 2134147
  have htrace : WordTrace (prefixWord ++ tailWord_2134147) baseStart_2134147 baseEnd_2134147 := by
    simpa [prefixWord, tailWord_2134147, baseEnd_2134147] using wordTrace_append hprefix tailTrace_2134147
  have hstable : (prefixWord ++ tailWord_2134147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134147).length < 2 ^ (prefixWord ++ tailWord_2134147).sum := by decide
  have hdescent : baseEnd_2134147 < baseStart_2134147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134159 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 7]
def baseStart_2134159 : Nat := 118140960795 + 2134159 * 2 ^ 59
def prefixEnd_2134159 : Nat := 4983230072969 + 3 ^ 40 * 2134159 * 2
def baseEnd_2134159 : Nat := 1095849360118820826797687

theorem tailTrace_2134159 : CollatzResearch.WordTrace tailWord_2134159 prefixEnd_2134159 1095849360118820826797687 := by
  unfold tailWord_2134159
  simp only [CollatzResearch.WordTrace]
  refine ⟨77839173475313903184149531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51892782316875935456099687 77839173475313903184149531)
  ·
    refine ⟨116758760212970854776224297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77839173475313903184149531 116758760212970854776224297)
    ·
      refine ⟨87569070159728141082168223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116758760212970854776224297 87569070159728141082168223)
      ·
        refine ⟨131353605239592211623252335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87569070159728141082168223 131353605239592211623252335)
        ·
          refine ⟨197030407859388317434878503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131353605239592211623252335 197030407859388317434878503)
          ·
            refine ⟨295545611789082476152317755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197030407859388317434878503 295545611789082476152317755)
            ·
              refine ⟨443318417683623714228476633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295545611789082476152317755 443318417683623714228476633)
              ·
                refine ⟨332488813262717785671357475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 443318417683623714228476633 332488813262717785671357475)
                ·
                  refine ⟨498733219894076678507036213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 332488813262717785671357475 498733219894076678507036213)
                  ·
                    refine ⟨46756239365069688610034645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 498733219894076678507036213 46756239365069688610034645)
                    ·
                      refine ⟨1095849360118820826797687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 46756239365069688610034645 1095849360118820826797687)
                      ·
                        rfl

theorem cell23_2134159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 7].length) (baseStart_2134159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134159 prefixEnd_2134159 := by exact prefixLift 2134159
  have htrace : WordTrace (prefixWord ++ tailWord_2134159) baseStart_2134159 baseEnd_2134159 := by
    simpa [prefixWord, tailWord_2134159, baseEnd_2134159] using wordTrace_append hprefix tailTrace_2134159
  have hstable : (prefixWord ++ tailWord_2134159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134159).length < 2 ^ (prefixWord ++ tailWord_2134159).sum := by decide
  have hdescent : baseEnd_2134159 < baseStart_2134159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134170 : List Nat := [3, 1, 1, 5, 2, 2, 2, 7]
def baseStart_2134170 : Nat := 118140960795 + 2134170 * 2 ^ 59
def prefixEnd_2134170 : Nat := 4983230072969 + 3 ^ 40 * 2134170 * 2
def baseEnd_2134170 : Nat := 40587222533556306805931

theorem tailTrace_2134170 : CollatzResearch.WordTrace tailWord_2134170 prefixEnd_2134170 40587222533556306805931 := by
  unfold tailWord_2134170
  simp only [CollatzResearch.WordTrace]
  refine ⟨19459893669568513015699991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51893049785516034708533309 19459893669568513015699991)
  ·
    refine ⟨29189840504352769523549987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19459893669568513015699991 29189840504352769523549987)
    ·
      refine ⟨43784760756529154285324981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29189840504352769523549987 43784760756529154285324981)
      ·
        refine ⟨4104821320924608214249217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43784760756529154285324981 4104821320924608214249217)
        ·
          refine ⟨3078615990693456160686913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4104821320924608214249217 3078615990693456160686913)
          ·
            refine ⟨2308961993020092120515185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3078615990693456160686913 2308961993020092120515185)
            ·
              refine ⟨1731721494765069090386389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2308961993020092120515185 1731721494765069090386389)
              ·
                refine ⟨40587222533556306805931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1731721494765069090386389 40587222533556306805931)
                ·
                  rfl

theorem cell23_2134170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 7].length) (baseStart_2134170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134170 prefixEnd_2134170 := by exact prefixLift 2134170
  have htrace : WordTrace (prefixWord ++ tailWord_2134170) baseStart_2134170 baseEnd_2134170 := by
    simpa [prefixWord, tailWord_2134170, baseEnd_2134170] using wordTrace_append hprefix tailTrace_2134170
  have hstable : (prefixWord ++ tailWord_2134170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134170).length < 2 ^ (prefixWord ++ tailWord_2134170).sum := by decide
  have hdescent : baseEnd_2134170 < baseStart_2134170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134176 : List Nat := [2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 5]
def baseStart_2134176 : Nat := 118140960795 + 2134176 * 2 ^ 59
def prefixEnd_2134176 : Nat := 4983230072969 + 3 ^ 40 * 2134176 * 2
def baseEnd_2134176 : Nat := 1095858089289947260285109

theorem tailTrace_2134176 : CollatzResearch.WordTrace tailWord_2134176 prefixEnd_2134176 1095858089289947260285109 := by
  unfold tailWord_2134176
  simp only [CollatzResearch.WordTrace]
  refine ⟨38919896758126157543759191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51893195677501543391678921 38919896758126157543759191)
  ·
    refine ⟨58379845137189236315638787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38919896758126157543759191 58379845137189236315638787)
    ·
      refine ⟨87569767705783854473458181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58379845137189236315638787 87569767705783854473458181)
      ·
        refine ⟨16419331444834472713773409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87569767705783854473458181 16419331444834472713773409)
        ·
          refine ⟨12314498583625854535330057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16419331444834472713773409 12314498583625854535330057)
          ·
            refine ⟨9235873937719390901497543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12314498583625854535330057 9235873937719390901497543)
            ·
              refine ⟨13853810906579086352246315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9235873937719390901497543 13853810906579086352246315)
              ·
                refine ⟨20780716359868629528369473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13853810906579086352246315 20780716359868629528369473)
                ·
                  refine ⟨15585537269901472146277105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20780716359868629528369473 15585537269901472146277105)
                  ·
                    refine ⟨11689152952426104109707829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15585537269901472146277105 11689152952426104109707829)
                    ·
                      refine ⟨1095858089289947260285109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11689152952426104109707829 1095858089289947260285109)
                      ·
                        rfl

theorem cell23_2134176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_2134176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134176 prefixEnd_2134176 := by exact prefixLift 2134176
  have htrace : WordTrace (prefixWord ++ tailWord_2134176) baseStart_2134176 baseEnd_2134176 := by
    simpa [prefixWord, tailWord_2134176, baseEnd_2134176] using wordTrace_append hprefix tailTrace_2134176
  have hstable : (prefixWord ++ tailWord_2134176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134176).length < 2 ^ (prefixWord ++ tailWord_2134176).sum := by decide
  have hdescent : baseEnd_2134176 < baseStart_2134176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134216 : List Nat := [2, 1, 3, 1, 2, 1, 1, 3, 1, 4, 4]
def baseStart_2134216 : Nat := 118140960795 + 2134216 * 2 ^ 59
def prefixEnd_2134216 : Nat := 4983230072969 + 3 ^ 40 * 2134216 * 2
def baseEnd_2134216 : Nat := 1095878628516127103784925

theorem tailTrace_2134216 : CollatzResearch.WordTrace tailWord_2134216 prefixEnd_2134216 1095878628516127103784925 := by
  unfold tailWord_2134216
  simp only [CollatzResearch.WordTrace]
  refine ⟨38920626218053700959487251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51894168290738267945983001 38920626218053700959487251)
  ·
    refine ⟨58380939327080551439230877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38920626218053700959487251 58380939327080551439230877)
    ·
      refine ⟨21892852247655206789711579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58380939327080551439230877 21892852247655206789711579)
      ·
        refine ⟨32839278371482810184567369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21892852247655206789711579 32839278371482810184567369)
        ·
          refine ⟨24629458778612107638425527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32839278371482810184567369 24629458778612107638425527)
          ·
            refine ⟨36944188167918161457638291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24629458778612107638425527 36944188167918161457638291)
            ·
              refine ⟨55416282251877242186457437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36944188167918161457638291 55416282251877242186457437)
              ·
                refine ⟨20781105844453965819921539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55416282251877242186457437 20781105844453965819921539)
                ·
                  refine ⟨31171658766680948729882309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20781105844453965819921539 31171658766680948729882309)
                  ·
                    refine ⟨5844686018752677886852933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31171658766680948729882309 5844686018752677886852933)
                    ·
                      refine ⟨1095878628516127103784925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5844686018752677886852933 1095878628516127103784925)
                      ·
                        rfl

theorem cell23_2134216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_2134216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134216 prefixEnd_2134216 := by exact prefixLift 2134216
  have htrace : WordTrace (prefixWord ++ tailWord_2134216) baseStart_2134216 baseEnd_2134216 := by
    simpa [prefixWord, tailWord_2134216, baseEnd_2134216] using wordTrace_append hprefix tailTrace_2134216
  have hstable : (prefixWord ++ tailWord_2134216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134216).length < 2 ^ (prefixWord ++ tailWord_2134216).sum := by decide
  have hdescent : baseEnd_2134216 < baseStart_2134216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134237 : List Nat := [1, 4, 3, 2, 1, 2, 1, 2, 1, 4, 2]
def baseStart_2134237 : Nat := 118140960795 + 2134237 * 2 ^ 59
def prefixEnd_2134237 : Nat := 4983230072969 + 3 ^ 40 * 2134237 * 2
def baseEnd_2134237 : Nat := 1095889411609871521622329

theorem tailTrace_2134237 : CollatzResearch.WordTrace tailWord_2134237 prefixEnd_2134237 1095889411609871521622329 := by
  unfold tailWord_2134237
  simp only [CollatzResearch.WordTrace]
  refine ⟨77842018369031322505488965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51894678912687548336992643 77842018369031322505488965)
  ·
    refine ⟨14595378444193372969779181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77842018369031322505488965 14595378444193372969779181)
    ·
      refine ⟨5473266916572514863667193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14595378444193372969779181 5473266916572514863667193)
      ·
        refine ⟨4104950187429386147750395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5473266916572514863667193 4104950187429386147750395)
        ·
          refine ⟨6157425281144079221625593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4104950187429386147750395 6157425281144079221625593)
          ·
            refine ⟨4618068960858059416219195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6157425281144079221625593 4618068960858059416219195)
            ·
              refine ⟨6927103441287089124328793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4618068960858059416219195 6927103441287089124328793)
              ·
                refine ⟨5195327580965316843246595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6927103441287089124328793 5195327580965316843246595)
                ·
                  refine ⟨7792991371447975264869893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5195327580965316843246595 7792991371447975264869893)
                  ·
                    refine ⟨1461185882146495362163105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7792991371447975264869893 1461185882146495362163105)
                    ·
                      refine ⟨1095889411609871521622329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1461185882146495362163105 1095889411609871521622329)
                      ·
                        rfl

theorem cell23_2134237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_2134237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134237 prefixEnd_2134237 := by exact prefixLift 2134237
  have htrace : WordTrace (prefixWord ++ tailWord_2134237) baseStart_2134237 baseEnd_2134237 := by
    simpa [prefixWord, tailWord_2134237, baseEnd_2134237] using wordTrace_append hprefix tailTrace_2134237
  have hstable : (prefixWord ++ tailWord_2134237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134237).length < 2 ^ (prefixWord ++ tailWord_2134237).sum := by decide
  have hdescent : baseEnd_2134237 < baseStart_2134237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134270 : List Nat := [4, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3]
def baseStart_2134270 : Nat := 118140960795 + 2134270 * 2 ^ 59
def prefixEnd_2134270 : Nat := 4983230072969 + 3 ^ 40 * 2134270 * 2
def baseEnd_2134270 : Nat := 1095906356471469892509677

theorem tailTrace_2134270 : CollatzResearch.WordTrace tailWord_2134270 prefixEnd_2134270 1095906356471469892509677 := by
  unfold tailWord_2134270
  simp only [CollatzResearch.WordTrace]
  refine ⟨9730402747238971142680033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51895481318607846094293509 9730402747238971142680033)
  ·
    refine ⟨7297802060429228357010025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9730402747238971142680033 7297802060429228357010025)
    ·
      refine ⟨5473351545321921267757519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7297802060429228357010025 5473351545321921267757519)
      ·
        refine ⟨8210027317982881901636279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5473351545321921267757519 8210027317982881901636279)
        ·
          refine ⟨12315040976974322852454419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8210027317982881901636279 12315040976974322852454419)
          ·
            refine ⟨18472561465461484278681629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12315040976974322852454419 18472561465461484278681629)
            ·
              refine ⟨6927210549548056604505611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18472561465461484278681629 6927210549548056604505611)
              ·
                refine ⟨10390815824322084906758417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6927210549548056604505611 10390815824322084906758417)
                ·
                  refine ⟨7793111868241563680068813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10390815824322084906758417 7793111868241563680068813)
                  ·
                    refine ⟨2922416950590586380025805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7793111868241563680068813 2922416950590586380025805)
                    ·
                      refine ⟨1095906356471469892509677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2922416950590586380025805 1095906356471469892509677)
                      ·
                        rfl

theorem cell23_2134270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_2134270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134270 prefixEnd_2134270 := by exact prefixLift 2134270
  have htrace : WordTrace (prefixWord ++ tailWord_2134270) baseStart_2134270 baseEnd_2134270 := by
    simpa [prefixWord, tailWord_2134270, baseEnd_2134270] using wordTrace_append hprefix tailTrace_2134270
  have hstable : (prefixWord ++ tailWord_2134270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134270).length < 2 ^ (prefixWord ++ tailWord_2134270).sum := by decide
  have hdescent : baseEnd_2134270 < baseStart_2134270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134343 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 2, 5, 3]
def baseStart_2134343 : Nat := 118140960795 + 2134343 * 2 ^ 59
def prefixEnd_2134343 : Nat := 4983230072969 + 3 ^ 40 * 2134343 * 2
def baseEnd_2134343 : Nat := 1095943840559248106896841

theorem tailTrace_2134343 : CollatzResearch.WordTrace tailWord_2134343 prefixEnd_2134343 1095943840559248106896841 := by
  unfold tailWord_2134343
  simp only [CollatzResearch.WordTrace]
  refine ⟨77845884506647302608847683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51897256337764868405898455 77845884506647302608847683)
  ·
    refine ⟨116768826759970953913271525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77845884506647302608847683 116768826759970953913271525)
    ·
      refine ⟨21894155017494553858738411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116768826759970953913271525 21894155017494553858738411)
      ·
        refine ⟨32841232526241830788107617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21894155017494553858738411 32841232526241830788107617)
        ·
          refine ⟨24630924394681373091080713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32841232526241830788107617 24630924394681373091080713)
          ·
            refine ⟨18473193296011029818310535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24630924394681373091080713 18473193296011029818310535)
            ·
              refine ⟨27709789944016544727465803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18473193296011029818310535 27709789944016544727465803)
              ·
                refine ⟨41564684916024817091198705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27709789944016544727465803 41564684916024817091198705)
                ·
                  refine ⟨31173513687018612818399029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41564684916024817091198705 31173513687018612818399029)
                  ·
                    refine ⟨2922516908157994951724909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31173513687018612818399029 2922516908157994951724909)
                    ·
                      refine ⟨1095943840559248106896841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2922516908157994951724909 1095943840559248106896841)
                      ·
                        rfl

theorem cell23_2134343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 5, 3].length) (baseStart_2134343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134343 prefixEnd_2134343 := by exact prefixLift 2134343
  have htrace : WordTrace (prefixWord ++ tailWord_2134343) baseStart_2134343 baseEnd_2134343 := by
    simpa [prefixWord, tailWord_2134343, baseEnd_2134343] using wordTrace_append hprefix tailTrace_2134343
  have hstable : (prefixWord ++ tailWord_2134343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134343).length < 2 ^ (prefixWord ++ tailWord_2134343).sum := by decide
  have hdescent : baseEnd_2134343 < baseStart_2134343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134364 : List Nat := [2, 2, 4, 3, 1, 1, 1, 2, 2, 2, 3]
def baseStart_2134364 : Nat := 118140960795 + 2134364 * 2 ^ 59
def prefixEnd_2134364 : Nat := 4983230072969 + 3 ^ 40 * 2134364 * 2
def baseEnd_2134364 : Nat := 1095954623652992524734245

theorem tailTrace_2134364 : CollatzResearch.WordTrace tailWord_2134364 prefixEnd_2134364 1095954623652992524734245 := by
  unfold tailWord_2134364
  simp only [CollatzResearch.WordTrace]
  refine ⟨38923325219785611597681073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51897766959714148796908097 38923325219785611597681073)
  ·
    refine ⟨29192493914839208698260805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38923325219785611597681073 29192493914839208698260805)
    ·
      refine ⟨5473592609032351630923901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29192493914839208698260805 5473592609032351630923901)
      ·
        refine ⟨2052597228387131861596463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5473592609032351630923901 2052597228387131861596463)
        ·
          refine ⟨3078895842580697792394695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2052597228387131861596463 3078895842580697792394695)
          ·
            refine ⟨4618343763871046688592043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3078895842580697792394695 4618343763871046688592043)
            ·
              refine ⟨6927515645806570032888065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4618343763871046688592043 6927515645806570032888065)
              ·
                refine ⟨5195636734354927524666049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6927515645806570032888065 5195636734354927524666049)
                ·
                  refine ⟨3896727550766195643499537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5195636734354927524666049 3896727550766195643499537)
                  ·
                    refine ⟨2922545663074646732624653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3896727550766195643499537 2922545663074646732624653)
                    ·
                      refine ⟨1095954623652992524734245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2922545663074646732624653 1095954623652992524734245)
                      ·
                        rfl

theorem cell23_2134364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_2134364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134364 prefixEnd_2134364 := by exact prefixLift 2134364
  have htrace : WordTrace (prefixWord ++ tailWord_2134364) baseStart_2134364 baseEnd_2134364 := by
    simpa [prefixWord, tailWord_2134364, baseEnd_2134364] using wordTrace_append hprefix tailTrace_2134364
  have hstable : (prefixWord ++ tailWord_2134364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134364).length < 2 ^ (prefixWord ++ tailWord_2134364).sum := by decide
  have hdescent : baseEnd_2134364 < baseStart_2134364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134393 : List Nat := [1, 2, 1, 3, 2, 1, 1, 5, 1, 6]
def baseStart_2134393 : Nat := 118140960795 + 2134393 * 2 ^ 59
def prefixEnd_2134393 : Nat := 4983230072969 + 3 ^ 40 * 2134393 * 2
def baseEnd_2134393 : Nat := 365323171530657637090537

theorem tailTrace_2134393 : CollatzResearch.WordTrace tailWord_2134393 prefixEnd_2134393 365323171530657637090537 := by
  unfold tailWord_2134393
  simp only [CollatzResearch.WordTrace]
  refine ⟨77847708156466161148167833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51898472104310774098778555 77847708156466161148167833)
  ·
    refine ⟨58385781117349620861125875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77847708156466161148167833 58385781117349620861125875)
    ·
      refine ⟨87578671676024431291688813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58385781117349620861125875 87578671676024431291688813)
      ·
        refine ⟨32842001878509161734383305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87578671676024431291688813 32842001878509161734383305)
        ·
          refine ⟨24631501408881871300787479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32842001878509161734383305 24631501408881871300787479)
          ·
            refine ⟨36947252113322806951181219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24631501408881871300787479 36947252113322806951181219)
            ·
              refine ⟨55420878169984210426771829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36947252113322806951181219 55420878169984210426771829)
              ·
                refine ⟨5195707328436019727509859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55420878169984210426771829 5195707328436019727509859)
                ·
                  refine ⟨7793560992654029591264789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5195707328436019727509859 7793560992654029591264789)
                  ·
                    refine ⟨365323171530657637090537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7793560992654029591264789 365323171530657637090537)
                    ·
                      rfl

theorem cell23_2134393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 6].length) (baseStart_2134393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134393 prefixEnd_2134393 := by exact prefixLift 2134393
  have htrace : WordTrace (prefixWord ++ tailWord_2134393) baseStart_2134393 baseEnd_2134393 := by
    simpa [prefixWord, tailWord_2134393, baseEnd_2134393] using wordTrace_append hprefix tailTrace_2134393
  have hstable : (prefixWord ++ tailWord_2134393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134393).length < 2 ^ (prefixWord ++ tailWord_2134393).sum := by decide
  have hdescent : baseEnd_2134393 < baseStart_2134393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134397 : List Nat := [1, 4, 1, 1, 2, 5, 1, 2, 1, 5]
def baseStart_2134397 : Nat := 118140960795 + 2134397 * 2 ^ 59
def prefixEnd_2134397 : Nat := 4983230072969 + 3 ^ 40 * 2134397 * 2
def baseEnd_2134397 : Nat := 365323856171530298540531

theorem tailTrace_2134397 : CollatzResearch.WordTrace tailWord_2134397 prefixEnd_2134397 365323856171530298540531 := by
  unfold tailWord_2134397
  simp only [CollatzResearch.WordTrace]
  refine ⟨77847854048451669831313445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51898569365634446554208963 77847854048451669831313445)
  ·
    refine ⟨14596472634084688093371271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77847854048451669831313445 14596472634084688093371271)
    ·
      refine ⟨21894708951127032140056907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14596472634084688093371271 21894708951127032140056907)
      ·
        refine ⟨32842063426690548210085361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21894708951127032140056907 32842063426690548210085361)
        ·
          refine ⟨24631547570017911157564021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32842063426690548210085361 24631547570017911157564021)
          ·
            refine ⟨2309207584689179171021627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24631547570017911157564021 2309207584689179171021627)
            ·
              refine ⟨3463811377033768756532441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2309207584689179171021627 3463811377033768756532441)
              ·
                refine ⟨2597858532775326567399331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3463811377033768756532441 2597858532775326567399331)
                ·
                  refine ⟨3896787799162989851098997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2597858532775326567399331 3896787799162989851098997)
                  ·
                    refine ⟨365323856171530298540531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3896787799162989851098997 365323856171530298540531)
                    ·
                      rfl

theorem cell23_2134397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 2, 1, 5].length) (baseStart_2134397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134397 prefixEnd_2134397 := by exact prefixLift 2134397
  have htrace : WordTrace (prefixWord ++ tailWord_2134397) baseStart_2134397 baseEnd_2134397 := by
    simpa [prefixWord, tailWord_2134397, baseEnd_2134397] using wordTrace_append hprefix tailTrace_2134397
  have hstable : (prefixWord ++ tailWord_2134397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134397).length < 2 ^ (prefixWord ++ tailWord_2134397).sum := by decide
  have hdescent : baseEnd_2134397 < baseStart_2134397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134414 : List Nat := [4, 1, 1, 4, 1, 2, 3, 1, 1, 5]
def baseStart_2134414 : Nat := 118140960795 + 2134414 * 2 ^ 59
def prefixEnd_2134414 : Nat := 4983230072969 + 3 ^ 40 * 2134414 * 2
def baseEnd_2134414 : Nat := 365326765895239109703005

theorem tailTrace_2134414 : CollatzResearch.WordTrace tailWord_2134414 prefixEnd_2134414 365326765895239109703005 := by
  unfold tailWord_2134414
  simp only [CollatzResearch.WordTrace]
  refine ⟨9731059261173760216835287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51898982726260054489788197 9731059261173760216835287)
  ·
    refine ⟨14596588891760640325252931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9731059261173760216835287 14596588891760640325252931)
    ·
      refine ⟨21894883337640960487879397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14596588891760640325252931 21894883337640960487879397)
      ·
        refine ⟨4105290625807680091477387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21894883337640960487879397 4105290625807680091477387)
        ·
          refine ⟨6157935938711520137216081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4105290625807680091477387 6157935938711520137216081)
          ·
            refine ⟨4618451954033640102912061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6157935938711520137216081 4618451954033640102912061)
            ·
              refine ⟨1731919482762615038592023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4618451954033640102912061 1731919482762615038592023)
              ·
                refine ⟨2597879224143922557888035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1731919482762615038592023 2597879224143922557888035)
                ·
                  refine ⟨3896818836215883836832053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2597879224143922557888035 3896818836215883836832053)
                  ·
                    refine ⟨365326765895239109703005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3896818836215883836832053 365326765895239109703005)
                    ·
                      rfl

theorem cell23_2134414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 1, 1, 5].length) (baseStart_2134414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134414 prefixEnd_2134414 := by exact prefixLift 2134414
  have htrace : WordTrace (prefixWord ++ tailWord_2134414) baseStart_2134414 baseEnd_2134414 := by
    simpa [prefixWord, tailWord_2134414, baseEnd_2134414] using wordTrace_append hprefix tailTrace_2134414
  have hstable : (prefixWord ++ tailWord_2134414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134414).length < 2 ^ (prefixWord ++ tailWord_2134414).sum := by decide
  have hdescent : baseEnd_2134414 < baseStart_2134414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134422 : List Nat := [5, 3, 1, 2, 1, 2, 2, 2, 1, 4]
def baseStart_2134422 : Nat := 118140960795 + 2134422 * 2 ^ 59
def prefixEnd_2134422 : Nat := 4983230072969 + 3 ^ 40 * 2134422 * 2
def baseEnd_2134422 : Nat := 365328135176984432602993

theorem tailTrace_2134422 : CollatzResearch.WordTrace tailWord_2134422 prefixEnd_2134422 365328135176984432602993 := by
  unfold tailWord_2134422
  simp only [CollatzResearch.WordTrace]
  refine ⟨4865547867085068693810845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51899177248907399400649013 4865547867085068693810845)
  ·
    refine ⟨1824580450156900760179067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4865547867085068693810845 1824580450156900760179067)
    ·
      refine ⟨2736870675235351140268601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1824580450156900760179067 2736870675235351140268601)
      ·
        refine ⟨2052653006426513355201451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2736870675235351140268601 2052653006426513355201451)
        ·
          refine ⟨3078979509639770032802177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2052653006426513355201451 3078979509639770032802177)
          ·
            refine ⟨2309234632229827524601633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3078979509639770032802177 2309234632229827524601633)
            ·
              refine ⟨1731925974172370643451225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2309234632229827524601633 1731925974172370643451225)
              ·
                refine ⟨1298944480629277982588419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1731925974172370643451225 1298944480629277982588419)
                ·
                  refine ⟨1948416720943916973882629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1298944480629277982588419 1948416720943916973882629)
                  ·
                    refine ⟨365328135176984432602993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1948416720943916973882629 365328135176984432602993)
                    ·
                      rfl

theorem cell23_2134422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_2134422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134422 prefixEnd_2134422 := by exact prefixLift 2134422
  have htrace : WordTrace (prefixWord ++ tailWord_2134422) baseStart_2134422 baseEnd_2134422 := by
    simpa [prefixWord, tailWord_2134422, baseEnd_2134422] using wordTrace_append hprefix tailTrace_2134422
  have hstable : (prefixWord ++ tailWord_2134422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134422).length < 2 ^ (prefixWord ++ tailWord_2134422).sum := by decide
  have hdescent : baseEnd_2134422 < baseStart_2134422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134434 : List Nat := [3, 3, 1, 2, 1, 1, 2, 3, 3, 2, 2]
def baseStart_2134434 : Nat := 118140960795 + 2134434 * 2 ^ 59
def prefixEnd_2134434 : Nat := 4983230072969 + 3 ^ 40 * 2134434 * 2
def baseEnd_2134434 : Nat := 1095990567298807250858923

theorem tailTrace_2134434 : CollatzResearch.WordTrace tailWord_2134434 prefixEnd_2134434 1095990567298807250858923 := by
  unfold tailWord_2134434
  simp only [CollatzResearch.WordTrace]
  refine ⟨19462300887329406287602589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51899469032878416766940237 19462300887329406287602589)
  ·
    refine ⟨7298362832748527357850971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19462300887329406287602589 7298362832748527357850971)
    ·
      refine ⟨10947544249122791036776457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7298362832748527357850971 10947544249122791036776457)
      ·
        refine ⟨8210658186842093277582343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10947544249122791036776457 8210658186842093277582343)
        ·
          refine ⟨12315987280263139916373515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8210658186842093277582343 12315987280263139916373515)
          ·
            refine ⟨18473980920394709874560273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12315987280263139916373515 18473980920394709874560273)
            ·
              refine ⟨13855485690296032405920205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18473980920394709874560273 13855485690296032405920205)
              ·
                refine ⟨5195807133861012152220077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13855485690296032405920205 5195807133861012152220077)
                ·
                  refine ⟨1948427675197879557082529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5195807133861012152220077 1948427675197879557082529)
                  ·
                    refine ⟨1461320756398409667811897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1948427675197879557082529 1461320756398409667811897)
                    ·
                      refine ⟨1095990567298807250858923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1461320756398409667811897 1095990567298807250858923)
                      ·
                        rfl

theorem cell23_2134434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_2134434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134434 prefixEnd_2134434 := by exact prefixLift 2134434
  have htrace : WordTrace (prefixWord ++ tailWord_2134434) baseStart_2134434 baseEnd_2134434 := by
    simpa [prefixWord, tailWord_2134434, baseEnd_2134434] using wordTrace_append hprefix tailTrace_2134434
  have hstable : (prefixWord ++ tailWord_2134434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134434).length < 2 ^ (prefixWord ++ tailWord_2134434).sum := by decide
  have hdescent : baseEnd_2134434 < baseStart_2134434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134465 : List Nat := [1, 2, 7, 1, 2, 1, 2, 1, 1, 5]
def baseStart_2134465 : Nat := 118140960795 + 2134465 * 2 ^ 59
def prefixEnd_2134465 : Nat := 4983230072969 + 3 ^ 40 * 2134465 * 2
def baseEnd_2134465 : Nat := 365335495066365543190427

theorem tailTrace_2134465 : CollatzResearch.WordTrace tailWord_2134465 prefixEnd_2134465 365335495066365543190427 := by
  unfold tailWord_2134465
  simp only [CollatzResearch.WordTrace]
  refine ⟨77850334212205317444788849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51900222808136878296525899 77850334212205317444788849)
  ·
    refine ⟨58387750659153988083591637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77850334212205317444788849 58387750659153988083591637)
    ·
      refine ⟨1368462906073921595709179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 58387750659153988083591637 1368462906073921595709179)
      ·
        refine ⟨2052694359110882393563769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1368462906073921595709179 2052694359110882393563769)
        ·
          refine ⟨1539520769333161795172827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2052694359110882393563769 1539520769333161795172827)
          ·
            refine ⟨2309281153999742692759241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1539520769333161795172827 2309281153999742692759241)
            ·
              refine ⟨1731960865499807019569431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2309281153999742692759241 1731960865499807019569431)
              ·
                refine ⟨2597941298249710529354147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1731960865499807019569431 2597941298249710529354147)
                ·
                  refine ⟨3896911947374565794031221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2597941298249710529354147 3896911947374565794031221)
                  ·
                    refine ⟨365335495066365543190427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3896911947374565794031221 365335495066365543190427)
                    ·
                      rfl

theorem cell23_2134465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_2134465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134465 prefixEnd_2134465 := by exact prefixLift 2134465
  have htrace : WordTrace (prefixWord ++ tailWord_2134465) baseStart_2134465 baseEnd_2134465 := by
    simpa [prefixWord, tailWord_2134465, baseEnd_2134465] using wordTrace_append hprefix tailTrace_2134465
  have hstable : (prefixWord ++ tailWord_2134465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134465).length < 2 ^ (prefixWord ++ tailWord_2134465).sum := by decide
  have hdescent : baseEnd_2134465 < baseStart_2134465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134468 : List Nat := [2, 3, 3, 2, 3, 1, 2, 1, 1, 1, 4]
def baseStart_2134468 : Nat := 118140960795 + 2134468 * 2 ^ 59
def prefixEnd_2134468 : Nat := 4983230072969 + 3 ^ 40 * 2134468 * 2
def baseEnd_2134468 : Nat := 1096008025641060117833767

theorem tailTrace_2134468 : CollatzResearch.WordTrace tailWord_2134468 prefixEnd_2134468 1096008025641060117833767 := by
  unfold tailWord_2134468
  simp only [CollatzResearch.WordTrace]
  refine ⟨38925221815597224478574029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51900295754129632638098705 38925221815597224478574029)
  ·
    refine ⟨14596958180848959179465261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38925221815597224478574029 14596958180848959179465261)
    ·
      refine ⟨5473859317818359692299473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14596958180848959179465261 5473859317818359692299473)
      ·
        refine ⟨4105394488363769769224605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5473859317818359692299473 4105394488363769769224605)
        ·
          refine ⟨1539522933136413663459227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4105394488363769769224605 1539522933136413663459227)
          ·
            refine ⟨2309284399704620495188841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1539522933136413663459227 2309284399704620495188841)
            ·
              refine ⟨1731963299778465371391631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2309284399704620495188841 1731963299778465371391631)
              ·
                refine ⟨2597944949667698057087447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1731963299778465371391631 2597944949667698057087447)
                ·
                  refine ⟨3896917424501547085631171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2597944949667698057087447 3896917424501547085631171)
                  ·
                    refine ⟨5845376136752320628446757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3896917424501547085631171 5845376136752320628446757)
                    ·
                      refine ⟨1096008025641060117833767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5845376136752320628446757 1096008025641060117833767)
                      ·
                        rfl

theorem cell23_2134468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_2134468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134468 prefixEnd_2134468 := by exact prefixLift 2134468
  have htrace : WordTrace (prefixWord ++ tailWord_2134468) baseStart_2134468 baseEnd_2134468 := by
    simpa [prefixWord, tailWord_2134468, baseEnd_2134468] using wordTrace_append hprefix tailTrace_2134468
  have hstable : (prefixWord ++ tailWord_2134468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134468).length < 2 ^ (prefixWord ++ tailWord_2134468).sum := by decide
  have hdescent : baseEnd_2134468 < baseStart_2134468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134484 : List Nat := [2, 4, 1, 2, 2, 2, 1, 1, 4, 1, 3]
def baseStart_2134484 : Nat := 118140960795 + 2134484 * 2 ^ 59
def prefixEnd_2134484 : Nat := 4983230072969 + 3 ^ 40 * 2134484 * 2
def baseEnd_2134484 : Nat := 1096016241331532055233693

theorem tailTrace_2134484 : CollatzResearch.WordTrace tailWord_2134484 prefixEnd_2134484 1096016241331532055233693 := by
  unfold tailWord_2134484
  simp only [CollatzResearch.WordTrace]
  refine ⟨38925513599568241844865253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51900684799424322459820337 38925513599568241844865253)
  ·
    refine ⟨7298533799919045345912235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38925513599568241844865253 7298533799919045345912235)
    ·
      refine ⟨10947800699878568018868353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7298533799919045345912235 10947800699878568018868353)
      ·
        refine ⟨8210850524908926014151265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10947800699878568018868353 8210850524908926014151265)
        ·
          refine ⟨6158137893681694510613449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8210850524908926014151265 6158137893681694510613449)
          ·
            refine ⟨4618603420261270882960087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6158137893681694510613449 4618603420261270882960087)
            ·
              refine ⟨6927905130391906324440131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4618603420261270882960087 6927905130391906324440131)
              ·
                refine ⟨10391857695587859486660197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6927905130391906324440131 10391857695587859486660197)
                ·
                  refine ⟨1948473317922723653748787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10391857695587859486660197 1948473317922723653748787)
                  ·
                    refine ⟨2922709976884085480623181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1948473317922723653748787 2922709976884085480623181)
                    ·
                      refine ⟨1096016241331532055233693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2922709976884085480623181 1096016241331532055233693)
                      ·
                        rfl

theorem cell23_2134484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_2134484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134484 prefixEnd_2134484 := by exact prefixLift 2134484
  have htrace : WordTrace (prefixWord ++ tailWord_2134484) baseStart_2134484 baseEnd_2134484 := by
    simpa [prefixWord, tailWord_2134484, baseEnd_2134484] using wordTrace_append hprefix tailTrace_2134484
  have hstable : (prefixWord ++ tailWord_2134484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134484).length < 2 ^ (prefixWord ++ tailWord_2134484).sum := by decide
  have hdescent : baseEnd_2134484 < baseStart_2134484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134498 : List Nat := [3, 3, 3, 2, 2, 1, 1, 1, 1, 2, 4]
def baseStart_2134498 : Nat := 118140960795 + 2134498 * 2 ^ 59
def prefixEnd_2134498 : Nat := 4983230072969 + 3 ^ 40 * 2134498 * 2
def baseEnd_2134498 : Nat := 1096023430060695000458629

theorem tailTrace_2134498 : CollatzResearch.WordTrace tailWord_2134498 prefixEnd_2134498 1096023430060695000458629 := by
  unfold tailWord_2134498
  simp only [CollatzResearch.WordTrace]
  refine ⟨19462884455271441020185037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51901025214057176053826765 19462884455271441020185037)
  ·
    refine ⟨7298581670726790382569389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19462884455271441020185037 7298581670726790382569389)
    ·
      refine ⟨2736968126522546393463521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7298581670726790382569389 2736968126522546393463521)
      ·
        refine ⟨2052726094891909795097641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2736968126522546393463521 2052726094891909795097641)
        ·
          refine ⟨1539544571168932346323231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2052726094891909795097641 1539544571168932346323231)
          ·
            refine ⟨2309316856753398519484847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1539544571168932346323231 2309316856753398519484847)
            ·
              refine ⟨3463975285130097779227271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2309316856753398519484847 3463975285130097779227271)
              ·
                refine ⟨5195962927695146668840907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3463975285130097779227271 5195962927695146668840907)
                ·
                  refine ⟨7793944391542720003261361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5195962927695146668840907 7793944391542720003261361)
                  ·
                    refine ⟨5845458293657040002446021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7793944391542720003261361 5845458293657040002446021)
                    ·
                      refine ⟨1096023430060695000458629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5845458293657040002446021 1096023430060695000458629)
                      ·
                        rfl

theorem cell23_2134498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_2134498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134498 prefixEnd_2134498 := by exact prefixLift 2134498
  have htrace : WordTrace (prefixWord ++ tailWord_2134498) baseStart_2134498 baseEnd_2134498 := by
    simpa [prefixWord, tailWord_2134498, baseEnd_2134498] using wordTrace_append hprefix tailTrace_2134498
  have hstable : (prefixWord ++ tailWord_2134498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134498).length < 2 ^ (prefixWord ++ tailWord_2134498).sum := by decide
  have hdescent : baseEnd_2134498 < baseStart_2134498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134501 : List Nat := [1, 3, 1, 5, 3, 1, 1, 1, 1, 3, 3]
def baseStart_2134501 : Nat := 118140960795 + 2134501 * 2 ^ 59
def prefixEnd_2134501 : Nat := 4983230072969 + 3 ^ 40 * 2134501 * 2
def baseEnd_2134501 : Nat := 1096024970502658488721115

theorem tailTrace_2134501 : CollatzResearch.WordTrace tailWord_2134501 prefixEnd_2134501 1096024970502658488721115 := by
  unfold tailWord_2134501
  simp only [CollatzResearch.WordTrace]
  refine ⟨77851647240074895593099357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51901098160049930395399571 77851647240074895593099357)
  ·
    refine ⟨29194367715028085847412259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77851647240074895593099357 29194367715028085847412259)
    ·
      refine ⟨43791551572542128771118389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29194367715028085847412259 43791551572542128771118389)
      ·
        refine ⟨4105457959925824572292349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43791551572542128771118389 4105457959925824572292349)
        ·
          refine ⟨1539546734972184214609631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4105457959925824572292349 1539546734972184214609631)
          ·
            refine ⟨2309320102458276321914447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1539546734972184214609631 2309320102458276321914447)
            ·
              refine ⟨3463980153687414482871671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2309320102458276321914447 3463980153687414482871671)
              ·
                refine ⟨5195970230531121724307507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3463980153687414482871671 5195970230531121724307507)
                ·
                  refine ⟨7793955345796682586461261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5195970230531121724307507 7793955345796682586461261)
                  ·
                    refine ⟨2922733254673755969922973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7793955345796682586461261 2922733254673755969922973)
                    ·
                      refine ⟨1096024970502658488721115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2922733254673755969922973 1096024970502658488721115)
                      ·
                        rfl

theorem cell23_2134501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_2134501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134501 prefixEnd_2134501 := by exact prefixLift 2134501
  have htrace : WordTrace (prefixWord ++ tailWord_2134501) baseStart_2134501 baseEnd_2134501 := by
    simpa [prefixWord, tailWord_2134501, baseEnd_2134501] using wordTrace_append hprefix tailTrace_2134501
  have hstable : (prefixWord ++ tailWord_2134501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134501).length < 2 ^ (prefixWord ++ tailWord_2134501).sum := by decide
  have hdescent : baseEnd_2134501 < baseStart_2134501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134523 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 7]
def baseStart_2134523 : Nat := 118140960795 + 2134523 * 2 ^ 59
def prefixEnd_2134523 : Nat := 4983230072969 + 3 ^ 40 * 2134523 * 2
def baseEnd_2134523 : Nat := 1096036267077057402646013

theorem tailTrace_2134523 : CollatzResearch.WordTrace tailWord_2134523 prefixEnd_2134523 1096036267077057402646013 := by
  unfold tailWord_2134523
  simp only [CollatzResearch.WordTrace]
  refine ⟨77852449645995193350400223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51901633097330128900266815 77852449645995193350400223)
  ·
    refine ⟨116778674468992790025600335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77852449645995193350400223 116778674468992790025600335)
    ·
      refine ⟨175168011703489185038400503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116778674468992790025600335 175168011703489185038400503)
      ·
        refine ⟨262752017555233777557600755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175168011703489185038400503 262752017555233777557600755)
        ·
          refine ⟨394128026332850666336401133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262752017555233777557600755 394128026332850666336401133)
          ·
            refine ⟨147798009874818999876150425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 394128026332850666336401133 147798009874818999876150425)
            ·
              refine ⟨110848507406114249907112819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147798009874818999876150425 110848507406114249907112819)
              ·
                refine ⟨166272761109171374860669229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110848507406114249907112819 166272761109171374860669229)
                ·
                  refine ⟨62352285415939265572750961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 166272761109171374860669229 62352285415939265572750961)
                  ·
                    refine ⟨46764214061954449179563221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 62352285415939265572750961 46764214061954449179563221)
                    ·
                      refine ⟨1096036267077057402646013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 46764214061954449179563221 1096036267077057402646013)
                      ·
                        rfl

theorem cell23_2134523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 7].length) (baseStart_2134523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134523 prefixEnd_2134523 := by exact prefixLift 2134523
  have htrace : WordTrace (prefixWord ++ tailWord_2134523) baseStart_2134523 baseEnd_2134523 := by
    simpa [prefixWord, tailWord_2134523, baseEnd_2134523] using wordTrace_append hprefix tailTrace_2134523
  have hstable : (prefixWord ++ tailWord_2134523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134523).length < 2 ^ (prefixWord ++ tailWord_2134523).sum := by decide
  have hdescent : baseEnd_2134523 < baseStart_2134523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134597 : List Nat := [1, 3, 1, 1, 1, 5, 2, 2, 2, 1, 4]
def baseStart_2134597 : Nat := 118140960795 + 2134597 * 2 ^ 59
def prefixEnd_2134597 : Nat := 4983230072969 + 3 ^ 40 * 2134597 * 2
def baseEnd_2134597 : Nat := 1096074264645490113120673

theorem tailTrace_2134597 : CollatzResearch.WordTrace tailWord_2134597 prefixEnd_2134597 1096074264645490113120673 := by
  unfold tailWord_2134597
  simp only [CollatzResearch.WordTrace]
  refine ⟨77855148647727103988594045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51903432431818069325729363 77855148647727103988594045)
  ·
    refine ⟨29195680742897663995722767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77855148647727103988594045 29195680742897663995722767)
    ·
      refine ⟨43793521114346495993584151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29195680742897663995722767 43793521114346495993584151)
      ·
        refine ⟨65690281671519743990376227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43793521114346495993584151 65690281671519743990376227)
        ·
          refine ⟨98535422507279615985564341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65690281671519743990376227 98535422507279615985564341)
          ·
            refine ⟨9237695860057463998646657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 98535422507279615985564341 9237695860057463998646657)
            ·
              refine ⟨6928271895043097998984993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9237695860057463998646657 6928271895043097998984993)
              ·
                refine ⟨5196203921282323499238745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6928271895043097998984993 5196203921282323499238745)
                ·
                  refine ⟨3897152940961742624429059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5196203921282323499238745 3897152940961742624429059)
                  ·
                    refine ⟨5845729411442613936643589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3897152940961742624429059 5845729411442613936643589)
                    ·
                      refine ⟨1096074264645490113120673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5845729411442613936643589 1096074264645490113120673)
                      ·
                        rfl

theorem cell23_2134597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 2, 1, 4].length) (baseStart_2134597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134597 prefixEnd_2134597 := by exact prefixLift 2134597
  have htrace : WordTrace (prefixWord ++ tailWord_2134597) baseStart_2134597 baseEnd_2134597 := by
    simpa [prefixWord, tailWord_2134597, baseEnd_2134597] using wordTrace_append hprefix tailTrace_2134597
  have hstable : (prefixWord ++ tailWord_2134597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134597).length < 2 ^ (prefixWord ++ tailWord_2134597).sum := by decide
  have hdescent : baseEnd_2134597 < baseStart_2134597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134598 : List Nat := [6, 1, 1, 1, 2, 1, 4, 2, 5]
def baseStart_2134598 : Nat := 118140960795 + 2134598 * 2 ^ 59
def prefixEnd_2134598 : Nat := 4983230072969 + 3 ^ 40 * 2134598 * 2
def baseEnd_2134598 : Nat := 121786086458460512134241

theorem tailTrace_2134598 : CollatzResearch.WordTrace tailWord_2134598 prefixEnd_2134598 121786086458460512134241 := by
  unfold tailWord_2134598
  simp only [CollatzResearch.WordTrace]
  refine ⟨2432974535022608786230639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 51903456747148987439586965 2432974535022608786230639)
  ·
    refine ⟨3649461802533913179345959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2432974535022608786230639 3649461802533913179345959)
    ·
      refine ⟨5474192703800869769018939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3649461802533913179345959 5474192703800869769018939)
      ·
        refine ⟨8211289055701304653528409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5474192703800869769018939 8211289055701304653528409)
        ·
          refine ⟨6158466791775978490146307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8211289055701304653528409 6158466791775978490146307)
          ·
            refine ⟨9237700187663967735219461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6158466791775978490146307 9237700187663967735219461)
            ·
              refine ⟨1732068785186993950353649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9237700187663967735219461 1732068785186993950353649)
              ·
                refine ⟨1299051588890245462765237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1732068785186993950353649 1299051588890245462765237)
                ·
                  refine ⟨121786086458460512134241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1299051588890245462765237 121786086458460512134241)
                  ·
                    rfl

theorem cell23_2134598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_2134598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134598 prefixEnd_2134598 := by exact prefixLift 2134598
  have htrace : WordTrace (prefixWord ++ tailWord_2134598) baseStart_2134598 baseEnd_2134598 := by
    simpa [prefixWord, tailWord_2134598, baseEnd_2134598] using wordTrace_append hprefix tailTrace_2134598
  have hstable : (prefixWord ++ tailWord_2134598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134598).length < 2 ^ (prefixWord ++ tailWord_2134598).sum := by decide
  have hdescent : baseEnd_2134598 < baseStart_2134598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134684 : List Nat := [2, 2, 3, 2, 2, 1, 1, 4, 1, 5]
def baseStart_2134684 : Nat := 118140960795 + 2134684 * 2 ^ 59
def prefixEnd_2134684 : Nat := 4983230072969 + 3 ^ 40 * 2134684 * 2
def baseEnd_2134684 : Nat := 365372979154143757577591

theorem tailTrace_2134684 : CollatzResearch.WordTrace tailWord_2134684 prefixEnd_2134684 365372979154143757577591 := by
  unfold tailWord_2134684
  simp only [CollatzResearch.WordTrace]
  refine ⟨38929160899205958923505553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51905547865607945231340737 38929160899205958923505553)
  ·
    refine ⟨29196870674404469192629165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38929160899205958923505553 29196870674404469192629165)
    ·
      refine ⟨10948826502901675947235937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29196870674404469192629165 10948826502901675947235937)
      ·
        refine ⟨8211619877176256960426953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10948826502901675947235937 8211619877176256960426953)
        ·
          refine ⟨6158714907882192720320215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8211619877176256960426953 6158714907882192720320215)
          ·
            refine ⟨9238072361823289080480323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6158714907882192720320215 9238072361823289080480323)
            ·
              refine ⟨13857108542734933620720485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9238072361823289080480323 13857108542734933620720485)
              ·
                refine ⟨2598207851762800053885091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13857108542734933620720485 2598207851762800053885091)
                ·
                  refine ⟨3897311777644200080827637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2598207851762800053885091 3897311777644200080827637)
                  ·
                    refine ⟨365372979154143757577591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3897311777644200080827637 365372979154143757577591)
                    ·
                      rfl

theorem cell23_2134684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_2134684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134684 prefixEnd_2134684 := by exact prefixLift 2134684
  have htrace : WordTrace (prefixWord ++ tailWord_2134684) baseStart_2134684 baseEnd_2134684 := by
    simpa [prefixWord, tailWord_2134684, baseEnd_2134684] using wordTrace_append hprefix tailTrace_2134684
  have hstable : (prefixWord ++ tailWord_2134684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134684).length < 2 ^ (prefixWord ++ tailWord_2134684).sum := by decide
  have hdescent : baseEnd_2134684 < baseStart_2134684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134697 : List Nat := [1, 2, 1, 1, 1, 1, 2, 6, 4, 4]
def baseStart_2134697 : Nat := 118140960795 + 2134697 * 2 ^ 59
def prefixEnd_2134697 : Nat := 4983230072969 + 3 ^ 40 * 2134697 * 2
def baseEnd_2134697 : Nat := 365375204236979907290071

theorem tailTrace_2134697 : CollatzResearch.WordTrace tailWord_2134697 prefixEnd_2134697 365375204236979907290071 := by
  unfold tailWord_2134697
  simp only [CollatzResearch.WordTrace]
  refine ⟨77858795947364821067234345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51905863964909880711489563 77858795947364821067234345)
  ·
    refine ⟨58394096960523615800425759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77858795947364821067234345 58394096960523615800425759)
    ·
      refine ⟨87591145440785423700638639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58394096960523615800425759 87591145440785423700638639)
      ·
        refine ⟨131386718161178135550957959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87591145440785423700638639 131386718161178135550957959)
        ·
          refine ⟨197080077241767203326436939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131386718161178135550957959 197080077241767203326436939)
          ·
            refine ⟨295620115862650804989655409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197080077241767203326436939 295620115862650804989655409)
            ·
              refine ⟨221715086896988103742241557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 295620115862650804989655409 221715086896988103742241557)
              ·
                refine ⟨10392894698296317362917573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 221715086896988103742241557 10392894698296317362917573)
                ·
                  refine ⟨1948667755930559505547045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10392894698296317362917573 1948667755930559505547045)
                  ·
                    refine ⟨365375204236979907290071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1948667755930559505547045 365375204236979907290071)
                    ·
                      rfl

theorem cell23_2134697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 4, 4].length) (baseStart_2134697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134697 prefixEnd_2134697 := by exact prefixLift 2134697
  have htrace : WordTrace (prefixWord ++ tailWord_2134697) baseStart_2134697 baseEnd_2134697 := by
    simpa [prefixWord, tailWord_2134697, baseEnd_2134697] using wordTrace_append hprefix tailTrace_2134697
  have hstable : (prefixWord ++ tailWord_2134697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134697).length < 2 ^ (prefixWord ++ tailWord_2134697).sum := by decide
  have hdescent : baseEnd_2134697 < baseStart_2134697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134707 : List Nat := [1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 5]
def baseStart_2134707 : Nat := 118140960795 + 2134707 * 2 ^ 59
def prefixEnd_2134707 : Nat := 4983230072969 + 3 ^ 40 * 2134707 * 2
def baseEnd_2134707 : Nat := 1096130747517484682745167

theorem tailTrace_2134707 : CollatzResearch.WordTrace tailWord_2134707 prefixEnd_2134707 1096130747517484682745167 := by
  unfold tailWord_2134707
  simp only [CollatzResearch.WordTrace]
  refine ⟨77859160677328592775098375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51906107118219061850065583 77859160677328592775098375)
  ·
    refine ⟨116788741015992889162647563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77859160677328592775098375 116788741015992889162647563)
    ·
      refine ⟨175183111523989333743971345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116788741015992889162647563 175183111523989333743971345)
      ·
        refine ⟨131387333642992000307978509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175183111523989333743971345 131387333642992000307978509)
        ·
          refine ⟨49270250116122000115491941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131387333642992000307978509 49270250116122000115491941)
          ·
            refine ⟨9238171896772875021654739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49270250116122000115491941 9238171896772875021654739)
            ·
              refine ⟨13857257845159312532482109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9238171896772875021654739 13857257845159312532482109)
              ·
                refine ⟨5196471691934742199680791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13857257845159312532482109 5196471691934742199680791)
                ·
                  refine ⟨7794707537902113299521187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5196471691934742199680791 7794707537902113299521187)
                  ·
                    refine ⟨11692061306853169949281781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7794707537902113299521187 11692061306853169949281781)
                    ·
                      refine ⟨1096130747517484682745167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11692061306853169949281781 1096130747517484682745167)
                      ·
                        rfl

theorem cell23_2134707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 5].length) (baseStart_2134707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134707 prefixEnd_2134707 := by exact prefixLift 2134707
  have htrace : WordTrace (prefixWord ++ tailWord_2134707) baseStart_2134707 baseEnd_2134707 := by
    simpa [prefixWord, tailWord_2134707, baseEnd_2134707] using wordTrace_append hprefix tailTrace_2134707
  have hstable : (prefixWord ++ tailWord_2134707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134707).length < 2 ^ (prefixWord ++ tailWord_2134707).sum := by decide
  have hdescent : baseEnd_2134707 < baseStart_2134707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134714 : List Nat := [3, 1, 1, 1, 2, 3, 2, 4, 2, 4]
def baseStart_2134714 : Nat := 118140960795 + 2134714 * 2 ^ 59
def prefixEnd_2134714 : Nat := 4983230072969 + 3 ^ 40 * 2134714 * 2
def baseEnd_2134714 : Nat := 365378113960688718452545

theorem tailTrace_2134714 : CollatzResearch.WordTrace tailWord_2134714 prefixEnd_2134714 365378113960688718452545 := by
  unfold tailWord_2134714
  simp only [CollatzResearch.WordTrace]
  refine ⟨19464853997075808242650799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51906277325535488647068797 19464853997075808242650799)
  ·
    refine ⟨29197280995613712363976199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19464853997075808242650799 29197280995613712363976199)
    ·
      refine ⟨43795921493420568545964299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29197280995613712363976199 43795921493420568545964299)
      ·
        refine ⟨65693882240130852818946449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43795921493420568545964299 65693882240130852818946449)
        ·
          refine ⟨49270411680098139614209837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65693882240130852818946449 49270411680098139614209837)
          ·
            refine ⟨18476404380036802355328689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49270411680098139614209837 18476404380036802355328689)
            ·
              refine ⟨13857303285027601766496517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18476404380036802355328689 13857303285027601766496517)
              ·
                refine ⟨2598244365942675331218097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13857303285027601766496517 2598244365942675331218097)
                ·
                  refine ⟨1948683274457006498413573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2598244365942675331218097 1948683274457006498413573)
                  ·
                    refine ⟨365378113960688718452545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1948683274457006498413573 365378113960688718452545)
                    ·
                      rfl

theorem cell23_2134714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 4, 2, 4].length) (baseStart_2134714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134714 prefixEnd_2134714 := by exact prefixLift 2134714
  have htrace : WordTrace (prefixWord ++ tailWord_2134714) baseStart_2134714 baseEnd_2134714 := by
    simpa [prefixWord, tailWord_2134714, baseEnd_2134714] using wordTrace_append hprefix tailTrace_2134714
  have hstable : (prefixWord ++ tailWord_2134714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134714).length < 2 ^ (prefixWord ++ tailWord_2134714).sum := by decide
  have hdescent : baseEnd_2134714 < baseStart_2134714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134717 : List Nat := [1, 4, 1, 2, 1, 3, 1, 2, 1, 1, 6]
def baseStart_2134717 : Nat := 118140960795 + 2134717 * 2 ^ 59
def prefixEnd_2134717 : Nat := 4983230072969 + 3 ^ 40 * 2134717 * 2
def baseEnd_2134717 : Nat := 1096135882324029643620121

theorem tailTrace_2134717 : CollatzResearch.WordTrace tailWord_2134717 prefixEnd_2134717 1096135882324029643620121 := by
  unfold tailWord_2134717
  simp only [CollatzResearch.WordTrace]
  refine ⟨77859525407292364482962405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51906350271528242988641603 77859525407292364482962405)
  ·
    refine ⟨14598661013867318340555451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77859525407292364482962405 14598661013867318340555451)
    ·
      refine ⟨21897991520800977510833177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14598661013867318340555451 21897991520800977510833177)
      ·
        refine ⟨16423493640600733133124883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21897991520800977510833177 16423493640600733133124883)
        ·
          refine ⟨24635240460901099699687325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16423493640600733133124883 24635240460901099699687325)
          ·
            refine ⟨9238215172837912387382747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24635240460901099699687325 9238215172837912387382747)
            ·
              refine ⟨13857322759256868581074121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9238215172837912387382747 13857322759256868581074121)
              ·
                refine ⟨10392992069442651435805591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13857322759256868581074121 10392992069442651435805591)
                ·
                  refine ⟨15589488104163977153708387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10392992069442651435805591 15589488104163977153708387)
                  ·
                    refine ⟨23384232156245965730562581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15589488104163977153708387 23384232156245965730562581)
                    ·
                      refine ⟨1096135882324029643620121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23384232156245965730562581 1096135882324029643620121)
                      ·
                        rfl

theorem cell23_2134717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_2134717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134717 prefixEnd_2134717 := by exact prefixLift 2134717
  have htrace : WordTrace (prefixWord ++ tailWord_2134717) baseStart_2134717 baseEnd_2134717 := by
    simpa [prefixWord, tailWord_2134717, baseEnd_2134717] using wordTrace_append hprefix tailTrace_2134717
  have hstable : (prefixWord ++ tailWord_2134717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134717).length < 2 ^ (prefixWord ++ tailWord_2134717).sum := by decide
  have hdescent : baseEnd_2134717 < baseStart_2134717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134724 : List Nat := [2, 3, 3, 1, 1, 2, 2, 2, 1, 1, 5]
def baseStart_2134724 : Nat := 118140960795 + 2134724 * 2 ^ 59
def prefixEnd_2134724 : Nat := 4983230072969 + 3 ^ 40 * 2134724 * 2
def baseEnd_2134724 : Nat := 1096139476688611116232589

theorem tailTrace_2134724 : CollatzResearch.WordTrace tailWord_2134724 prefixEnd_2134724 1096139476688611116232589 := by
  unfold tailWord_2134724
  simp only [CollatzResearch.WordTrace]
  refine ⟨38929890359133502339233613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51906520478844669785644817 38929890359133502339233613)
  ·
    refine ⟨14598708884675063377212605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38929890359133502339233613 14598708884675063377212605)
    ·
      refine ⟨5474515831753148766454727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14598708884675063377212605 5474515831753148766454727)
      ·
        refine ⟨8211773747629723149682091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5474515831753148766454727 8211773747629723149682091)
        ·
          refine ⟨12317660621444584724523137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8211773747629723149682091 12317660621444584724523137)
          ·
            refine ⟨9238245466083438543392353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12317660621444584724523137 9238245466083438543392353)
            ·
              refine ⟨6928684099562578907544265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9238245466083438543392353 6928684099562578907544265)
              ·
                refine ⟨5196513074671934180658199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6928684099562578907544265 5196513074671934180658199)
                ·
                  refine ⟨7794769612007901270987299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5196513074671934180658199 7794769612007901270987299)
                  ·
                    refine ⟨11692154418011851906480949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7794769612007901270987299 11692154418011851906480949)
                    ·
                      refine ⟨1096139476688611116232589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11692154418011851906480949 1096139476688611116232589)
                      ·
                        rfl

theorem cell23_2134724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_2134724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134724 prefixEnd_2134724 := by exact prefixLift 2134724
  have htrace : WordTrace (prefixWord ++ tailWord_2134724) baseStart_2134724 baseEnd_2134724 := by
    simpa [prefixWord, tailWord_2134724, baseEnd_2134724] using wordTrace_append hprefix tailTrace_2134724
  have hstable : (prefixWord ++ tailWord_2134724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134724).length < 2 ^ (prefixWord ++ tailWord_2134724).sum := by decide
  have hdescent : baseEnd_2134724 < baseStart_2134724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134738 : List Nat := [3, 2, 2, 2, 3, 2, 1, 2, 1, 1, 4]
def baseStart_2134738 : Nat := 118140960795 + 2134738 * 2 ^ 59
def prefixEnd_2134738 : Nat := 4983230072969 + 3 ^ 40 * 2134738 * 2
def baseEnd_2134738 : Nat := 1096146665417774061457525

theorem tailTrace_2134738 : CollatzResearch.WordTrace tailWord_2134738 prefixEnd_2134738 1096146665417774061457525 := by
  unfold tailWord_2134738
  simp only [CollatzResearch.WordTrace]
  refine ⟨19465072835054071267369217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51906860893477523379651245 19465072835054071267369217)
  ·
    refine ⟨14598804626290553450526913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19465072835054071267369217 14598804626290553450526913)
    ·
      refine ⟨10949103469717915087895185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14598804626290553450526913 10949103469717915087895185)
      ·
        refine ⟨8211827602288436315921389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10949103469717915087895185 8211827602288436315921389)
        ·
          refine ⟨3079435350858163618470521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8211827602288436315921389 3079435350858163618470521)
          ·
            refine ⟨2309576513143622713852891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3079435350858163618470521 2309576513143622713852891)
            ·
              refine ⟨3464364769715434070779337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2309576513143622713852891 3464364769715434070779337)
              ·
                refine ⟨2598273577286575553084503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3464364769715434070779337 2598273577286575553084503)
                ·
                  refine ⟨3897410365929863329626755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2598273577286575553084503 3897410365929863329626755)
                  ·
                    refine ⟨5846115548894794994440133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3897410365929863329626755 5846115548894794994440133)
                    ·
                      refine ⟨1096146665417774061457525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5846115548894794994440133 1096146665417774061457525)
                      ·
                        rfl

theorem cell23_2134738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_2134738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134738 prefixEnd_2134738 := by exact prefixLift 2134738
  have htrace : WordTrace (prefixWord ++ tailWord_2134738) baseStart_2134738 baseEnd_2134738 := by
    simpa [prefixWord, tailWord_2134738, baseEnd_2134738] using wordTrace_append hprefix tailTrace_2134738
  have hstable : (prefixWord ++ tailWord_2134738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134738).length < 2 ^ (prefixWord ++ tailWord_2134738).sum := by decide
  have hdescent : baseEnd_2134738 < baseStart_2134738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134815 : List Nat := [1, 1, 2, 4, 2, 4, 2, 1, 1, 3, 2]
def baseStart_2134815 : Nat := 118140960795 + 2134815 * 2 ^ 59
def prefixEnd_2134815 : Nat := 4983230072969 + 3 ^ 40 * 2134815 * 2
def baseEnd_2134815 : Nat := 1096186203428170260194671

theorem tailTrace_2134815 : CollatzResearch.WordTrace tailWord_2134815 prefixEnd_2134815 1096186203428170260194671 := by
  unfold tailWord_2134815
  simp only [CollatzResearch.WordTrace]
  refine ⟨77863099760937327220029899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51908733173958218146686599 77863099760937327220029899)
  ·
    refine ⟨116794649641405990830044849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77863099760937327220029899 116794649641405990830044849)
    ·
      refine ⟨87595987231054493122533637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116794649641405990830044849 87595987231054493122533637)
      ·
        refine ⟨16424247605822717460475057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87595987231054493122533637 16424247605822717460475057)
        ·
          refine ⟨12318185704367038095356293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16424247605822717460475057 12318185704367038095356293)
          ·
            refine ⟨2309659819568819642879305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12318185704367038095356293 2309659819568819642879305)
            ·
              refine ⟨1732244864676614732159479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2309659819568819642879305 1732244864676614732159479)
              ·
                refine ⟨2598367297014922098239219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1732244864676614732159479 2598367297014922098239219)
                ·
                  refine ⟨3897550945522383147358829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2598367297014922098239219 3897550945522383147358829)
                  ·
                    refine ⟨1461581604570893680259561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3897550945522383147358829 1461581604570893680259561)
                    ·
                      refine ⟨1096186203428170260194671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1461581604570893680259561 1096186203428170260194671)
                      ·
                        rfl

theorem cell23_2134815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 1, 1, 3, 2].length) (baseStart_2134815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134815 prefixEnd_2134815 := by exact prefixLift 2134815
  have htrace : WordTrace (prefixWord ++ tailWord_2134815) baseStart_2134815 baseEnd_2134815 := by
    simpa [prefixWord, tailWord_2134815, baseEnd_2134815] using wordTrace_append hprefix tailTrace_2134815
  have hstable : (prefixWord ++ tailWord_2134815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134815).length < 2 ^ (prefixWord ++ tailWord_2134815).sum := by decide
  have hdescent : baseEnd_2134815 < baseStart_2134815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134817 : List Nat := [1, 2, 3, 2, 1, 2, 1, 2, 9]
def baseStart_2134817 : Nat := 118140960795 + 2134817 * 2 ^ 59
def prefixEnd_2134817 : Nat := 4983230072969 + 3 ^ 40 * 2134817 * 2
def baseEnd_2134817 : Nat := 121798581154386583596629

theorem tailTrace_2134817 : CollatzResearch.WordTrace tailWord_2134817 prefixEnd_2134817 121798581154386583596629 := by
  unfold tailWord_2134817
  simp only [CollatzResearch.WordTrace]
  refine ⟨77863172706930081561602705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51908781804620054374401803 77863172706930081561602705)
  ·
    refine ⟨58397379530197561171202029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77863172706930081561602705 58397379530197561171202029)
    ·
      refine ⟨21899017323824085439200761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58397379530197561171202029 21899017323824085439200761)
      ·
        refine ⟨16424262992868064079400571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21899017323824085439200761 16424262992868064079400571)
        ·
          refine ⟨24636394489302096119100857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16424262992868064079400571 24636394489302096119100857)
          ·
            refine ⟨18477295866976572089325643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24636394489302096119100857 18477295866976572089325643)
            ·
              refine ⟨27715943800464858133988465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18477295866976572089325643 27715943800464858133988465)
              ·
                refine ⟨20786957850348643600491349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27715943800464858133988465 20786957850348643600491349)
                ·
                  refine ⟨121798581154386583596629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 20786957850348643600491349 121798581154386583596629)
                  ·
                    rfl

theorem cell23_2134817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 9].length) (baseStart_2134817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134817 prefixEnd_2134817 := by exact prefixLift 2134817
  have htrace : WordTrace (prefixWord ++ tailWord_2134817) baseStart_2134817 baseEnd_2134817 := by
    simpa [prefixWord, tailWord_2134817, baseEnd_2134817] using wordTrace_append hprefix tailTrace_2134817
  have hstable : (prefixWord ++ tailWord_2134817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134817).length < 2 ^ (prefixWord ++ tailWord_2134817).sum := by decide
  have hdescent : baseEnd_2134817 < baseStart_2134817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134824 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 4, 2, 4]
def baseStart_2134824 : Nat := 118140960795 + 2134824 * 2 ^ 59
def prefixEnd_2134824 : Nat := 4983230072969 + 3 ^ 40 * 2134824 * 2
def baseEnd_2134824 : Nat := 1096190824754060724982129

theorem tailTrace_2134824 : CollatzResearch.WordTrace tailWord_2134824 prefixEnd_2134824 1096190824754060724982129 := by
  unfold tailWord_2134824
  simp only [CollatzResearch.WordTrace]
  refine ⟨38931714008952360878553763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51908952011936481171405017 38931714008952360878553763)
  ·
    refine ⟨58397571013428541317830645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38931714008952360878553763 58397571013428541317830645)
    ·
      refine ⟨5474772282508925748546623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58397571013428541317830645 5474772282508925748546623)
      ·
        refine ⟨8212158423763388622819935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5474772282508925748546623 8212158423763388622819935)
        ·
          refine ⟨12318237635645082934229903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8212158423763388622819935 12318237635645082934229903)
          ·
            refine ⟨18477356453467624401344855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12318237635645082934229903 18477356453467624401344855)
            ·
              refine ⟨27716034680201436602017283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18477356453467624401344855 27716034680201436602017283)
              ·
                refine ⟨41574052020302154903025925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27716034680201436602017283 41574052020302154903025925)
                ·
                  refine ⟨7795134753806654044317361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41574052020302154903025925 7795134753806654044317361)
                  ·
                    refine ⟨5846351065354990533238021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7795134753806654044317361 5846351065354990533238021)
                    ·
                      refine ⟨1096190824754060724982129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5846351065354990533238021 1096190824754060724982129)
                      ·
                        rfl

theorem cell23_2134824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_2134824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134824 prefixEnd_2134824 := by exact prefixLift 2134824
  have htrace : WordTrace (prefixWord ++ tailWord_2134824) baseStart_2134824 baseEnd_2134824 := by
    simpa [prefixWord, tailWord_2134824, baseEnd_2134824] using wordTrace_append hprefix tailTrace_2134824
  have hstable : (prefixWord ++ tailWord_2134824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134824).length < 2 ^ (prefixWord ++ tailWord_2134824).sum := by decide
  have hdescent : baseEnd_2134824 < baseStart_2134824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134834 : List Nat := [3, 2, 1, 1, 3, 1, 4, 1, 7]
def baseStart_2134834 : Nat := 118140960795 + 2134834 * 2 ^ 59
def prefixEnd_2134834 : Nat := 4983230072969 + 3 ^ 40 * 2134834 * 2
def baseEnd_2134834 : Nat := 121799551062289520650787

theorem tailTrace_2134834 : CollatzResearch.WordTrace tailWord_2134834 prefixEnd_2134834 121799551062289520650787 := by
  unfold tailWord_2134834
  simp only [CollatzResearch.WordTrace]
  refine ⟨19465948186967123366242889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51909195165245662309981037 19465948186967123366242889)
  ·
    refine ⟨14599461140225342524682167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19465948186967123366242889 14599461140225342524682167)
    ·
      refine ⟨21899191710338013787023251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14599461140225342524682167 21899191710338013787023251)
      ·
        refine ⟨32848787565507020680534877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21899191710338013787023251 32848787565507020680534877)
        ·
          refine ⟨12318295337065132755200579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32848787565507020680534877 12318295337065132755200579)
          ·
            refine ⟨18477443005597699132800869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12318295337065132755200579 18477443005597699132800869)
            ·
              refine ⟨3464520563549568587400163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18477443005597699132800869 3464520563549568587400163)
              ·
                refine ⟨5196780845324352881100245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3464520563549568587400163 5196780845324352881100245)
                ·
                  refine ⟨121799551062289520650787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5196780845324352881100245 121799551062289520650787)
                  ·
                    rfl

theorem cell23_2134834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 7].length) (baseStart_2134834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134834 prefixEnd_2134834 := by exact prefixLift 2134834
  have htrace : WordTrace (prefixWord ++ tailWord_2134834) baseStart_2134834 baseEnd_2134834 := by
    simpa [prefixWord, tailWord_2134834, baseEnd_2134834] using wordTrace_append hprefix tailTrace_2134834
  have hstable : (prefixWord ++ tailWord_2134834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134834).length < 2 ^ (prefixWord ++ tailWord_2134834).sum := by decide
  have hdescent : baseEnd_2134834 < baseStart_2134834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134845 : List Nat := [1, 4, 1, 4, 2, 2, 1, 1, 1, 4, 2]
def baseStart_2134845 : Nat := 118140960795 + 2134845 * 2 ^ 59
def prefixEnd_2134845 : Nat := 4983230072969 + 3 ^ 40 * 2134845 * 2
def baseEnd_2134845 : Nat := 1096201607847805142819533

theorem tailTrace_2134845 : CollatzResearch.WordTrace tailWord_2134845 prefixEnd_2134845 1096201607847805142819533 := by
  unfold tailWord_2134845
  simp only [CollatzResearch.WordTrace]
  refine ⟨77864193950828642343621989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51909462633885761562414659 77864193950828642343621989)
  ·
    refine ⟨14599536365780370439429123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77864193950828642343621989 14599536365780370439429123)
    ·
      refine ⟨21899304548670555659143685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14599536365780370439429123 21899304548670555659143685)
      ·
        refine ⟨4106119602875729186089441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21899304548670555659143685 4106119602875729186089441)
        ·
          refine ⟨3079589702156796889567081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4106119602875729186089441 3079589702156796889567081)
          ·
            refine ⟨2309692276617597667175311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3079589702156796889567081 2309692276617597667175311)
            ·
              refine ⟨3464538414926396500762967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2309692276617597667175311 3464538414926396500762967)
              ·
                refine ⟨5196807622389594751144451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3464538414926396500762967 5196807622389594751144451)
                ·
                  refine ⟨7795211433584392126716677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5196807622389594751144451 7795211433584392126716677)
                  ·
                    refine ⟨1461602143797073523759377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7795211433584392126716677 1461602143797073523759377)
                    ·
                      refine ⟨1096201607847805142819533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1461602143797073523759377 1096201607847805142819533)
                      ·
                        rfl

theorem cell23_2134845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_2134845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134845 prefixEnd_2134845 := by exact prefixLift 2134845
  have htrace : WordTrace (prefixWord ++ tailWord_2134845) baseStart_2134845 baseEnd_2134845 := by
    simpa [prefixWord, tailWord_2134845, baseEnd_2134845] using wordTrace_append hprefix tailTrace_2134845
  have hstable : (prefixWord ++ tailWord_2134845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134845).length < 2 ^ (prefixWord ++ tailWord_2134845).sum := by decide
  have hdescent : baseEnd_2134845 < baseStart_2134845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134904 : List Nat := [2, 1, 2, 1, 1, 1, 1, 6, 1, 4, 3]
def baseStart_2134904 : Nat := 118140960795 + 2134904 * 2 ^ 59
def prefixEnd_2134904 : Nat := 4983230072969 + 3 ^ 40 * 2134904 * 2
def baseEnd_2134904 : Nat := 1096231903206420411981761

theorem tailTrace_2134904 : CollatzResearch.WordTrace tailWord_2134904 prefixEnd_2134904 1096231903206420411981761 := by
  unfold tailWord_2134904
  simp only [CollatzResearch.WordTrace]
  refine ⟨38933172928807447710009883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51910897238409930280013177 38933172928807447710009883)
  ·
    refine ⟨58399759393211171565014825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38933172928807447710009883 58399759393211171565014825)
    ·
      refine ⟨43799819544908378673761119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58399759393211171565014825 43799819544908378673761119)
      ·
        refine ⟨65699729317362568010641679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43799819544908378673761119 65699729317362568010641679)
        ·
          refine ⟨98549593976043852015962519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65699729317362568010641679 98549593976043852015962519)
          ·
            refine ⟨147824390964065778023943779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98549593976043852015962519 147824390964065778023943779)
            ·
              refine ⟨221736586446098667035915669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147824390964065778023943779 221736586446098667035915669)
              ·
                refine ⟨10393902489660875017308547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 221736586446098667035915669 10393902489660875017308547)
                ·
                  refine ⟨15590853734491312525962821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10393902489660875017308547 15590853734491312525962821)
                  ·
                    refine ⟨2923285075217121098618029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15590853734491312525962821 2923285075217121098618029)
                    ·
                      refine ⟨1096231903206420411981761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2923285075217121098618029 1096231903206420411981761)
                      ·
                        rfl

theorem cell23_2134904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 1, 4, 3].length) (baseStart_2134904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134904 prefixEnd_2134904 := by exact prefixLift 2134904
  have htrace : WordTrace (prefixWord ++ tailWord_2134904) baseStart_2134904 baseEnd_2134904 := by
    simpa [prefixWord, tailWord_2134904, baseEnd_2134904] using wordTrace_append hprefix tailTrace_2134904
  have hstable : (prefixWord ++ tailWord_2134904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134904).length < 2 ^ (prefixWord ++ tailWord_2134904).sum := by decide
  have hdescent : baseEnd_2134904 < baseStart_2134904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134921 : List Nat := [1, 2, 1, 1, 5, 2, 1, 3, 2, 2, 3]
def baseStart_2134921 : Nat := 118140960795 + 2134921 * 2 ^ 59
def prefixEnd_2134921 : Nat := 4983230072969 + 3 ^ 40 * 2134921 * 2
def baseEnd_2134921 : Nat := 1096240632377546845469183

theorem tailTrace_2134921 : CollatzResearch.WordTrace tailWord_2134921 prefixEnd_2134921 1096240632377546845469183 := by
  unfold tailWord_2134921
  simp only [CollatzResearch.WordTrace]
  refine ⟨77866965898553307323388617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51911310599035538215592411 77866965898553307323388617)
  ·
    refine ⟨58400224423914980492541463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77866965898553307323388617 58400224423914980492541463)
    ·
      refine ⟨87600336635872470738812195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58400224423914980492541463 87600336635872470738812195)
      ·
        refine ⟨131400504953808706108218293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87600336635872470738812195 131400504953808706108218293)
        ·
          refine ⟨12318797339419566197645465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 131400504953808706108218293 12318797339419566197645465)
          ·
            refine ⟨9239098004564674648234099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12318797339419566197645465 9239098004564674648234099)
            ·
              refine ⟨13858647006847011972351149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9239098004564674648234099 13858647006847011972351149)
              ·
                refine ⟨5196992627567629489631681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13858647006847011972351149 5196992627567629489631681)
                ·
                  refine ⟨3897744470675722117223761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5196992627567629489631681 3897744470675722117223761)
                  ·
                    refine ⟨2923308353006791587917821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3897744470675722117223761 2923308353006791587917821)
                    ·
                      refine ⟨1096240632377546845469183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2923308353006791587917821 1096240632377546845469183)
                      ·
                        rfl

theorem cell23_2134921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 2, 2, 3].length) (baseStart_2134921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134921 prefixEnd_2134921 := by exact prefixLift 2134921
  have htrace : WordTrace (prefixWord ++ tailWord_2134921) baseStart_2134921 baseEnd_2134921 := by
    simpa [prefixWord, tailWord_2134921, baseEnd_2134921] using wordTrace_append hprefix tailTrace_2134921
  have hstable : (prefixWord ++ tailWord_2134921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134921).length < 2 ^ (prefixWord ++ tailWord_2134921).sum := by decide
  have hdescent : baseEnd_2134921 < baseStart_2134921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134941 : List Nat := [1, 4, 2, 1, 2, 1, 4, 2, 6]
def baseStart_2134941 : Nat := 118140960795 + 2134941 * 2 ^ 59
def prefixEnd_2134941 : Nat := 4983230072969 + 3 ^ 40 * 2134941 * 2
def baseEnd_2134941 : Nat := 121805655776737418579899

theorem tailTrace_2134941 : CollatzResearch.WordTrace tailWord_2134941 prefixEnd_2134941 121805655776737418579899 := by
  unfold tailWord_2134941
  simp only [CollatzResearch.WordTrace]
  refine ⟨77867695358480850739116677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51911796905653900492744451 77867695358480850739116677)
  ·
    refine ⟨14600192879715159513584377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77867695358480850739116677 14600192879715159513584377)
    ·
      refine ⟨10950144659786369635188283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14600192879715159513584377 10950144659786369635188283)
      ·
        refine ⟨16425216989679554452782425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10950144659786369635188283 16425216989679554452782425)
        ·
          refine ⟨12318912742259665839586819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16425216989679554452782425 12318912742259665839586819)
          ·
            refine ⟨18478369113389498759380229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12318912742259665839586819 18478369113389498759380229)
            ·
              refine ⟨3464694208760531017383793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18478369113389498759380229 3464694208760531017383793)
              ·
                refine ⟨2598520656570398263037845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3464694208760531017383793 2598520656570398263037845)
                ·
                  refine ⟨121805655776737418579899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2598520656570398263037845 121805655776737418579899)
                  ·
                    rfl

theorem cell23_2134941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 2, 6].length) (baseStart_2134941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134941 prefixEnd_2134941 := by exact prefixLift 2134941
  have htrace : WordTrace (prefixWord ++ tailWord_2134941) baseStart_2134941 baseEnd_2134941 := by
    simpa [prefixWord, tailWord_2134941, baseEnd_2134941] using wordTrace_append hprefix tailTrace_2134941
  have hstable : (prefixWord ++ tailWord_2134941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134941).length < 2 ^ (prefixWord ++ tailWord_2134941).sum := by decide
  have hdescent : baseEnd_2134941 < baseStart_2134941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134945 : List Nat := [1, 2, 3, 4, 1, 2, 1, 4, 1, 4]
def baseStart_2134945 : Nat := 118140960795 + 2134945 * 2 ^ 59
def prefixEnd_2134945 : Nat := 4983230072969 + 3 ^ 40 * 2134945 * 2
def baseEnd_2134945 : Nat := 365417651971084917189691

theorem tailTrace_2134945 : CollatzResearch.WordTrace tailWord_2134945 prefixEnd_2134945 365417651971084917189691 := by
  unfold tailWord_2134945
  simp only [CollatzResearch.WordTrace]
  refine ⟨77867841250466359422262289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51911894166977572948174859 77867841250466359422262289)
  ·
    refine ⟨58400880937849769566696717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77867841250466359422262289 58400880937849769566696717)
    ·
      refine ⟨21900330351693663587511269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58400880937849769566696717 21900330351693663587511269)
      ·
        refine ⟨4106311940942561922658363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21900330351693663587511269 4106311940942561922658363)
        ·
          refine ⟨6159467911413842883987545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4106311940942561922658363 6159467911413842883987545)
          ·
            refine ⟨4619600933560382162990659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6159467911413842883987545 4619600933560382162990659)
            ·
              refine ⟨6929401400340573244485989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4619600933560382162990659 6929401400340573244485989)
              ·
                refine ⟨1299262762563857483341123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6929401400340573244485989 1299262762563857483341123)
                ·
                  refine ⟨1948894143845786225011685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1299262762563857483341123 1948894143845786225011685)
                  ·
                    refine ⟨365417651971084917189691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1948894143845786225011685 365417651971084917189691)
                    ·
                      rfl

theorem cell23_2134945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 4, 1, 4].length) (baseStart_2134945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134945 prefixEnd_2134945 := by exact prefixLift 2134945
  have htrace : WordTrace (prefixWord ++ tailWord_2134945) baseStart_2134945 baseEnd_2134945 := by
    simpa [prefixWord, tailWord_2134945, baseEnd_2134945] using wordTrace_append hprefix tailTrace_2134945
  have hstable : (prefixWord ++ tailWord_2134945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134945).length < 2 ^ (prefixWord ++ tailWord_2134945).sum := by decide
  have hdescent : baseEnd_2134945 < baseStart_2134945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134968 : List Nat := [2, 1, 2, 1, 2, 5, 1, 2, 3, 1, 3]
def baseStart_2134968 : Nat := 118140960795 + 2134968 * 2 ^ 59
def prefixEnd_2134968 : Nat := 4983230072969 + 3 ^ 40 * 2134968 * 2
def baseEnd_2134968 : Nat := 1096264765968308161581467

theorem tailTrace_2134968 : CollatzResearch.WordTrace tailWord_2134968 prefixEnd_2134968 1096264765968308161581467 := by
  unfold tailWord_2134968
  simp only [CollatzResearch.WordTrace]
  refine ⟨38934340064691517175174779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51912453419588689566899705 38934340064691517175174779)
  ·
    refine ⟨58401510097037275762762169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38934340064691517175174779 58401510097037275762762169)
    ·
      refine ⟨43801132572777956822071627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58401510097037275762762169 43801132572777956822071627)
      ·
        refine ⟨65701698859166935233107441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43801132572777956822071627 65701698859166935233107441)
        ·
          refine ⟨49276274144375201424830581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65701698859166935233107441 49276274144375201424830581)
          ·
            refine ⟨4619650701035175133577867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49276274144375201424830581 4619650701035175133577867)
            ·
              refine ⟨6929476051552762700366801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4619650701035175133577867 6929476051552762700366801)
              ·
                refine ⟨5197107038664572025275101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6929476051552762700366801 5197107038664572025275101)
                ·
                  refine ⟨1948915139499214509478163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5197107038664572025275101 1948915139499214509478163)
                  ·
                    refine ⟨2923372709248821764217245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1948915139499214509478163 2923372709248821764217245)
                    ·
                      refine ⟨1096264765968308161581467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2923372709248821764217245 1096264765968308161581467)
                      ·
                        rfl

theorem cell23_2134968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 3, 1, 3].length) (baseStart_2134968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2134968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2134968 prefixEnd_2134968 := by exact prefixLift 2134968
  have htrace : WordTrace (prefixWord ++ tailWord_2134968) baseStart_2134968 baseEnd_2134968 := by
    simpa [prefixWord, tailWord_2134968, baseEnd_2134968] using wordTrace_append hprefix tailTrace_2134968
  have hstable : (prefixWord ++ tailWord_2134968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134968).length < 2 ^ (prefixWord ++ tailWord_2134968).sum := by decide
  have hdescent : baseEnd_2134968 < baseStart_2134968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135011 : List Nat := [1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 5]
def baseStart_2135011 : Nat := 118140960795 + 2135011 * 2 ^ 59
def prefixEnd_2135011 : Nat := 4983230072969 + 3 ^ 40 * 2135011 * 2
def baseEnd_2135011 : Nat := 1096286845636451493343769

theorem tailTrace_2135011 : CollatzResearch.WordTrace tailWord_2135011 prefixEnd_2135011 1096286845636451493343769 := by
  unfold tailWord_2135011
  simp only [CollatzResearch.WordTrace]
  refine ⟨77870248468227252694164887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51913498978818168462776591 77870248468227252694164887)
  ·
    refine ⟨116805372702340879041247331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77870248468227252694164887 116805372702340879041247331)
    ·
      refine ⟨175208059053511318561870997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116805372702340879041247331 175208059053511318561870997)
      ·
        refine ⟨8212877768133343057587703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 175208059053511318561870997 8212877768133343057587703)
        ·
          refine ⟨12319316652200014586381555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8212877768133343057587703 12319316652200014586381555)
          ·
            refine ⟨18478974978300021879572333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12319316652200014586381555 18478974978300021879572333)
            ·
              refine ⟨6929615616862508204839625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18478974978300021879572333 6929615616862508204839625)
              ·
                refine ⟨5197211712646881153629719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6929615616862508204839625 5197211712646881153629719)
                ·
                  refine ⟨7795817568970321730444579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5197211712646881153629719 7795817568970321730444579)
                  ·
                    refine ⟨11693726353455482595666869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7795817568970321730444579 11693726353455482595666869)
                    ·
                      refine ⟨1096286845636451493343769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11693726353455482595666869 1096286845636451493343769)
                      ·
                        rfl

theorem cell23_2135011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_2135011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135011 prefixEnd_2135011 := by exact prefixLift 2135011
  have htrace : WordTrace (prefixWord ++ tailWord_2135011) baseStart_2135011 baseEnd_2135011 := by
    simpa [prefixWord, tailWord_2135011, baseEnd_2135011] using wordTrace_append hprefix tailTrace_2135011
  have hstable : (prefixWord ++ tailWord_2135011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135011).length < 2 ^ (prefixWord ++ tailWord_2135011).sum := by decide
  have hdescent : baseEnd_2135011 < baseStart_2135011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135018 : List Nat := [3, 1, 3, 1, 2, 4, 1, 1, 1, 6]
def baseStart_2135018 : Nat := 118140960795 + 2135018 * 2 ^ 59
def prefixEnd_2135018 : Nat := 4983230072969 + 3 ^ 40 * 2135018 * 2
def baseEnd_2135018 : Nat := 365430146667010988652079

theorem tailTrace_2135018 : CollatzResearch.WordTrace tailWord_2135018 prefixEnd_2135018 365430146667010988652079 := by
  unfold tailWord_2135018
  simp only [CollatzResearch.WordTrace]
  refine ⟨19467625944800473222417427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51913669186134595259779805 19467625944800473222417427)
  ·
    refine ⟨29201438917200709833626141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19467625944800473222417427 29201438917200709833626141)
    ·
      refine ⟨10950539593950266187609803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29201438917200709833626141 10950539593950266187609803)
      ·
        refine ⟨16425809390925399281414705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10950539593950266187609803 16425809390925399281414705)
        ·
          refine ⟨12319357043194049461061029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16425809390925399281414705 12319357043194049461061029)
          ·
            refine ⟨2309879445598884273948943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12319357043194049461061029 2309879445598884273948943)
            ·
              refine ⟨3464819168398326410923415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2309879445598884273948943 3464819168398326410923415)
              ·
                refine ⟨5197228752597489616385123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3464819168398326410923415 5197228752597489616385123)
                ·
                  refine ⟨7795843128896234424577685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5197228752597489616385123 7795843128896234424577685)
                  ·
                    refine ⟨365430146667010988652079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7795843128896234424577685 365430146667010988652079)
                    ·
                      rfl

theorem cell23_2135018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_2135018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135018 prefixEnd_2135018 := by exact prefixLift 2135018
  have htrace : WordTrace (prefixWord ++ tailWord_2135018) baseStart_2135018 baseEnd_2135018 := by
    simpa [prefixWord, tailWord_2135018, baseEnd_2135018] using wordTrace_append hprefix tailTrace_2135018
  have hstable : (prefixWord ++ tailWord_2135018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135018).length < 2 ^ (prefixWord ++ tailWord_2135018).sum := by decide
  have hdescent : baseEnd_2135018 < baseStart_2135018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135025 : List Nat := [1, 2, 2, 2, 4, 1, 2, 2, 3, 2, 2]
def baseStart_2135025 : Nat := 118140960795 + 2135025 * 2 ^ 59
def prefixEnd_2135025 : Nat := 4983230072969 + 3 ^ 40 * 2135025 * 2
def baseEnd_2135025 : Nat := 1096294034365614438568705

theorem tailTrace_2135025 : CollatzResearch.WordTrace tailWord_2135025 prefixEnd_2135025 1096294034365614438568705 := by
  unfold tailWord_2135025
  simp only [CollatzResearch.WordTrace]
  refine ⟨77870759090176533085174529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51913839393451022056783019 77870759090176533085174529)
  ·
    refine ⟨58403069317632399813880897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77870759090176533085174529 58403069317632399813880897)
    ·
      refine ⟨43802301988224299860410673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58403069317632399813880897 43802301988224299860410673)
      ·
        refine ⟨32851726491168224895308005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43802301988224299860410673 32851726491168224895308005)
        ·
          refine ⟨6159698717094042167870251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32851726491168224895308005 6159698717094042167870251)
          ·
            refine ⟨9239548075641063251805377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6159698717094042167870251 9239548075641063251805377)
            ·
              refine ⟨6929661056730797438854033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9239548075641063251805377 6929661056730797438854033)
              ·
                refine ⟨5197245792548098079140525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6929661056730797438854033 5197245792548098079140525)
                ·
                  refine ⟨1948967172205536779677697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5197245792548098079140525 1948967172205536779677697)
                  ·
                    refine ⟨1461725379154152584758273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1948967172205536779677697 1461725379154152584758273)
                    ·
                      refine ⟨1096294034365614438568705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1461725379154152584758273 1096294034365614438568705)
                      ·
                        rfl

theorem cell23_2135025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 3, 2, 2].length) (baseStart_2135025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135025 prefixEnd_2135025 := by exact prefixLift 2135025
  have htrace : WordTrace (prefixWord ++ tailWord_2135025) baseStart_2135025 baseEnd_2135025 := by
    simpa [prefixWord, tailWord_2135025, baseEnd_2135025] using wordTrace_append hprefix tailTrace_2135025
  have hstable : (prefixWord ++ tailWord_2135025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135025).length < 2 ^ (prefixWord ++ tailWord_2135025).sum := by decide
  have hdescent : baseEnd_2135025 < baseStart_2135025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135034 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 1, 4, 6]
def baseStart_2135034 : Nat := 118140960795 + 2135034 * 2 ^ 59
def prefixEnd_2135034 : Nat := 4983230072969 + 3 ^ 40 * 2135034 * 2
def baseEnd_2135034 : Nat := 1096298655691504903356163

theorem tailTrace_2135034 : CollatzResearch.WordTrace tailWord_2135034 prefixEnd_2135034 1096298655691504903356163 := by
  unfold tailWord_2135034
  simp only [CollatzResearch.WordTrace]
  refine ⟨19467771836785981905563039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51914058231429285081501437 19467771836785981905563039)
  ·
    refine ⟨29201657755178972858344559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19467771836785981905563039 29201657755178972858344559)
    ·
      refine ⟨43802486632768459287516839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29201657755178972858344559 43802486632768459287516839)
      ·
        refine ⟨65703729949152688931275259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43802486632768459287516839 65703729949152688931275259)
        ·
          refine ⟨98555594923729033396912889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65703729949152688931275259 98555594923729033396912889)
          ·
            refine ⟨73916696192796775047684667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98555594923729033396912889 73916696192796775047684667)
            ·
              refine ⟨110875044289195162571527001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73916696192796775047684667 110875044289195162571527001)
              ·
                refine ⟨83156283216896371928645251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110875044289195162571527001 83156283216896371928645251)
                ·
                  refine ⟨124734424825344557892967877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83156283216896371928645251 124734424825344557892967877)
                  ·
                    refine ⟨23387704654752104604931477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 124734424825344557892967877 23387704654752104604931477)
                    ·
                      refine ⟨1096298655691504903356163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23387704654752104604931477 1096298655691504903356163)
                      ·
                        rfl

theorem cell23_2135034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_2135034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135034 prefixEnd_2135034 := by exact prefixLift 2135034
  have htrace : WordTrace (prefixWord ++ tailWord_2135034) baseStart_2135034 baseEnd_2135034 := by
    simpa [prefixWord, tailWord_2135034, baseEnd_2135034] using wordTrace_append hprefix tailTrace_2135034
  have hstable : (prefixWord ++ tailWord_2135034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135034).length < 2 ^ (prefixWord ++ tailWord_2135034).sum := by decide
  have hdescent : baseEnd_2135034 < baseStart_2135034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135069 : List Nat := [1, 4, 2, 2, 4, 1, 2, 1, 2, 4]
def baseStart_2135069 : Nat := 118140960795 + 2135069 * 2 ^ 59
def prefixEnd_2135069 : Nat := 4983230072969 + 3 ^ 40 * 2135069 * 2
def baseEnd_2135069 : Nat := 365438875838137422139501

theorem tailTrace_2135069 : CollatzResearch.WordTrace tailWord_2135069 prefixEnd_2135069 365438875838137422139501 := by
  unfold tailWord_2135069
  simp only [CollatzResearch.WordTrace]
  refine ⟨77872363902017128599776261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51914909268011419066517507 77872363902017128599776261)
  ·
    refine ⟨14601068231628211612458049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77872363902017128599776261 14601068231628211612458049)
    ·
      refine ⟨10950801173721158709343537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14601068231628211612458049 10950801173721158709343537)
      ·
        refine ⟨8213100880290869032007653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10950801173721158709343537 8213100880290869032007653)
        ·
          refine ⟨1539956415054537943501435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8213100880290869032007653 1539956415054537943501435)
          ·
            refine ⟨2309934622581806915252153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1539956415054537943501435 2309934622581806915252153)
            ·
              refine ⟨1732450966936355186439115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2309934622581806915252153 1732450966936355186439115)
              ·
                refine ⟨2598676450404532779658673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1732450966936355186439115 2598676450404532779658673)
                ·
                  refine ⟨1949007337803399584744005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2598676450404532779658673 1949007337803399584744005)
                  ·
                    refine ⟨365438875838137422139501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1949007337803399584744005 365438875838137422139501)
                    ·
                      rfl

theorem cell23_2135069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_2135069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135069 prefixEnd_2135069 := by exact prefixLift 2135069
  have htrace : WordTrace (prefixWord ++ tailWord_2135069) baseStart_2135069 baseEnd_2135069 := by
    simpa [prefixWord, tailWord_2135069, baseEnd_2135069] using wordTrace_append hprefix tailTrace_2135069
  have hstable : (prefixWord ++ tailWord_2135069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135069).length < 2 ^ (prefixWord ++ tailWord_2135069).sum := by decide
  have hdescent : baseEnd_2135069 < baseStart_2135069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135075 : List Nat := [1, 1, 1, 4, 3, 3, 1, 3, 2, 1, 3]
def baseStart_2135075 : Nat := 118140960795 + 2135075 * 2 ^ 59
def prefixEnd_2135075 : Nat := 4983230072969 + 3 ^ 40 * 2135075 * 2
def baseEnd_2135075 : Nat := 1096319708398339242943475

theorem tailTrace_2135075 : CollatzResearch.WordTrace tailWord_2135075 prefixEnd_2135075 1096319708398339242943475 := by
  unfold tailWord_2135075
  simp only [CollatzResearch.WordTrace]
  refine ⟨77872582739995391624494679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51915055159996927749663119 77872582739995391624494679)
  ·
    refine ⟨116808874109993087436742019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77872582739995391624494679 116808874109993087436742019)
    ·
      refine ⟨175213311164989631155113029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116808874109993087436742019 175213311164989631155113029)
      ·
        refine ⟨32852495843435555841583693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 175213311164989631155113029 32852495843435555841583693)
        ·
          refine ⟨12319685941288333440593885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32852495843435555841583693 12319685941288333440593885)
          ·
            refine ⟨4619882227983125040222707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12319685941288333440593885 4619882227983125040222707)
            ·
              refine ⟨6929823341974687560334061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4619882227983125040222707 6929823341974687560334061)
              ·
                refine ⟨2598683753240507835125273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6929823341974687560334061 2598683753240507835125273)
                ·
                  refine ⟨1949012814930380876343955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2598683753240507835125273 1949012814930380876343955)
                  ·
                    refine ⟨2923519222395571314515933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1949012814930380876343955 2923519222395571314515933)
                    ·
                      refine ⟨1096319708398339242943475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2923519222395571314515933 1096319708398339242943475)
                      ·
                        rfl

theorem cell23_2135075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 3, 2, 1, 3].length) (baseStart_2135075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135075 prefixEnd_2135075 := by exact prefixLift 2135075
  have htrace : WordTrace (prefixWord ++ tailWord_2135075) baseStart_2135075 baseEnd_2135075 := by
    simpa [prefixWord, tailWord_2135075, baseEnd_2135075] using wordTrace_append hprefix tailTrace_2135075
  have hstable : (prefixWord ++ tailWord_2135075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135075).length < 2 ^ (prefixWord ++ tailWord_2135075).sum := by decide
  have hdescent : baseEnd_2135075 < baseStart_2135075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135098 : List Nat := [3, 1, 1, 1, 3, 1, 3, 1, 3, 4, 2]
def baseStart_2135098 : Nat := 118140960795 + 2135098 * 2 ^ 59
def prefixEnd_2135098 : Nat := 4983230072969 + 3 ^ 40 * 2135098 * 2
def baseEnd_2135098 : Nat := 1096331518453392652955869

theorem tailTrace_2135098 : CollatzResearch.WordTrace tailWord_2135098 prefixEnd_2135098 1096331518453392652955869 := by
  unfold tailWord_2135098
  simp only [CollatzResearch.WordTrace]
  refine ⟨19468355404728016638145487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51915614412608044368387965 19468355404728016638145487)
  ·
    refine ⟨29202533107092024957218231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19468355404728016638145487 29202533107092024957218231)
    ·
      refine ⟨43803799660638037435827347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29202533107092024957218231 43803799660638037435827347)
      ·
        refine ⟨65705699490957056153741021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43803799660638037435827347 65705699490957056153741021)
        ·
          refine ⟨24639637309108896057652883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65705699490957056153741021 24639637309108896057652883)
          ·
            refine ⟨36959455963663344086479325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24639637309108896057652883 36959455963663344086479325)
            ·
              refine ⟨13859795986373754032429747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36959455963663344086479325 13859795986373754032429747)
              ·
                refine ⟨20789693979560631048644621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13859795986373754032429747 20789693979560631048644621)
                ·
                  refine ⟨7796135242335236643241733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20789693979560631048644621 7796135242335236643241733)
                  ·
                    refine ⟨1461775357937856870607825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7796135242335236643241733 1461775357937856870607825)
                    ·
                      refine ⟨1096331518453392652955869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1461775357937856870607825 1096331518453392652955869)
                      ·
                        rfl

theorem cell23_2135098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 3, 4, 2].length) (baseStart_2135098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135098 prefixEnd_2135098 := by exact prefixLift 2135098
  have htrace : WordTrace (prefixWord ++ tailWord_2135098) baseStart_2135098 baseEnd_2135098 := by
    simpa [prefixWord, tailWord_2135098, baseEnd_2135098] using wordTrace_append hprefix tailTrace_2135098
  have hstable : (prefixWord ++ tailWord_2135098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135098).length < 2 ^ (prefixWord ++ tailWord_2135098).sum := by decide
  have hdescent : baseEnd_2135098 < baseStart_2135098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135132 : List Nat := [2, 2, 4, 1, 1, 1, 1, 5, 2, 2, 2]
def baseStart_2135132 : Nat := 118140960795 + 2135132 * 2 ^ 59
def prefixEnd_2135132 : Nat := 4983230072969 + 3 ^ 40 * 2135132 * 2
def baseEnd_2135132 : Nat := 1096348976795645519930713

theorem tailTrace_2135132 : CollatzResearch.WordTrace tailWord_2135132 prefixEnd_2135132 1096348976795645519930713 := by
  unfold tailWord_2135132
  simp only [CollatzResearch.WordTrace]
  refine ⟨38937330850394445179659825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51916441133859260239546433 38937330850394445179659825)
  ·
    refine ⟨29202998137795833884744869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38937330850394445179659825 29202998137795833884744869)
    ·
      refine ⟨5475562150836718853389663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29202998137795833884744869 5475562150836718853389663)
      ·
        refine ⟨8213343226255078280084495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5475562150836718853389663 8213343226255078280084495)
        ·
          refine ⟨12320014839382617420126743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8213343226255078280084495 12320014839382617420126743)
          ·
            refine ⟨18480022259073926130190115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12320014839382617420126743 18480022259073926130190115)
            ·
              refine ⟨27720033388610889195285173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18480022259073926130190115 27720033388610889195285173)
              ·
                refine ⟨2598753130182270862057985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27720033388610889195285173 2598753130182270862057985)
                ·
                  refine ⟨1949064847636703146543489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2598753130182270862057985 1949064847636703146543489)
                  ·
                    refine ⟨1461798635727527359907617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1949064847636703146543489 1461798635727527359907617)
                    ·
                      refine ⟨1096348976795645519930713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1461798635727527359907617 1096348976795645519930713)
                      ·
                        rfl

theorem cell23_2135132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_2135132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135132 prefixEnd_2135132 := by exact prefixLift 2135132
  have htrace : WordTrace (prefixWord ++ tailWord_2135132) baseStart_2135132 baseEnd_2135132 := by
    simpa [prefixWord, tailWord_2135132, baseEnd_2135132] using wordTrace_append hprefix tailTrace_2135132
  have hstable : (prefixWord ++ tailWord_2135132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135132).length < 2 ^ (prefixWord ++ tailWord_2135132).sum := by decide
  have hdescent : baseEnd_2135132 < baseStart_2135132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135138 : List Nat := [3, 3, 2, 2, 1, 1, 1, 1, 9]
def baseStart_2135138 : Nat := 118140960795 + 2135138 * 2 ^ 59
def prefixEnd_2135138 : Nat := 4983230072969 + 3 ^ 40 * 2135138 * 2
def baseEnd_2135138 : Nat := 121816895297730277383965

theorem tailTrace_2135138 : CollatzResearch.WordTrace tailWord_2135138 prefixEnd_2135138 121816895297730277383965 := by
  unfold tailWord_2135138
  simp only [CollatzResearch.WordTrace]
  refine ⟨19468720134691788346009517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51916587025844768922692045 19468720134691788346009517)
  ·
    refine ⟨7300770050509420629753569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19468720134691788346009517 7300770050509420629753569)
    ·
      refine ⟨5475577537882065472315177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7300770050509420629753569 5475577537882065472315177)
      ·
        refine ⟨4106683153411549104236383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5475577537882065472315177 4106683153411549104236383)
        ·
          refine ⟨6160024730117323656354575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4106683153411549104236383 6160024730117323656354575)
          ·
            refine ⟨9240037095175985484531863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6160024730117323656354575 9240037095175985484531863)
            ·
              refine ⟨13860055642763978226797795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9240037095175985484531863 13860055642763978226797795)
              ·
                refine ⟨20790083464145967340196693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13860055642763978226797795 20790083464145967340196693)
                ·
                  refine ⟨121816895297730277383965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 20790083464145967340196693 121816895297730277383965)
                  ·
                    rfl

theorem cell23_2135138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_2135138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135138 prefixEnd_2135138 := by exact prefixLift 2135138
  have htrace : WordTrace (prefixWord ++ tailWord_2135138) baseStart_2135138 baseEnd_2135138 := by
    simpa [prefixWord, tailWord_2135138, baseEnd_2135138] using wordTrace_append hprefix tailTrace_2135138
  have hstable : (prefixWord ++ tailWord_2135138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135138).length < 2 ^ (prefixWord ++ tailWord_2135138).sum := by decide
  have hdescent : baseEnd_2135138 < baseStart_2135138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135151 : List Nat := [1, 1, 2, 1, 3, 3, 3, 1, 1, 7]
def baseStart_2135151 : Nat := 118140960795 + 2135151 * 2 ^ 59
def prefixEnd_2135151 : Nat := 4983230072969 + 3 ^ 40 * 2135151 * 2
def baseEnd_2135151 : Nat := 365452910976026981864375

theorem tailTrace_2135151 : CollatzResearch.WordTrace tailWord_2135151 prefixEnd_2135151 365452910976026981864375 := by
  unfold tailWord_2135151
  simp only [CollatzResearch.WordTrace]
  refine ⟨77875354687720056604261307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51916903125146704402840871 77875354687720056604261307)
  ·
    refine ⟨116813032031580084906391961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77875354687720056604261307 116813032031580084906391961)
    ·
      refine ⟨87609774023685063679793971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116813032031580084906391961 87609774023685063679793971)
      ·
        refine ⟨131414661035527595519690957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87609774023685063679793971 131414661035527595519690957)
        ·
          refine ⟨49280497888322848319884109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131414661035527595519690957 49280497888322848319884109)
          ·
            refine ⟨18480186708121068119956541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49280497888322848319884109 18480186708121068119956541)
            ·
              refine ⟨6930070015545400544983703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18480186708121068119956541 6930070015545400544983703)
              ·
                refine ⟨10395105023318100817475555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6930070015545400544983703 10395105023318100817475555)
                ·
                  refine ⟨15592657534977151226213333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10395105023318100817475555 15592657534977151226213333)
                  ·
                    refine ⟨365452910976026981864375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15592657534977151226213333 365452910976026981864375)
                    ·
                      rfl

theorem cell23_2135151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 7].length) (baseStart_2135151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135151 prefixEnd_2135151 := by exact prefixLift 2135151
  have htrace : WordTrace (prefixWord ++ tailWord_2135151) baseStart_2135151 baseEnd_2135151 := by
    simpa [prefixWord, tailWord_2135151, baseEnd_2135151] using wordTrace_append hprefix tailTrace_2135151
  have hstable : (prefixWord ++ tailWord_2135151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135151).length < 2 ^ (prefixWord ++ tailWord_2135151).sum := by decide
  have hdescent : baseEnd_2135151 < baseStart_2135151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
