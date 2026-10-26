import V185TrunkScan23Chunk0806

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4773514 : List Nat := [3, 1, 2, 3, 2, 2, 3, 1, 1, 1, 4]
def baseStart_4773514 : Nat := 118140960795 + 4773514 * 2 ^ 59
def prefixEnd_4773514 : Nat := 4983230072969 + 3 ^ 40 * 4773514 * 2
def baseEnd_4773514 : Nat := 2451107092966341838222015

theorem tailTrace_4773514 : CollatzResearch.WordTrace tailWord_4773514 prefixEnd_4773514 2451107092966341838222015 := by
  unfold tailWord_4773514
  simp only [CollatzResearch.WordTrace]
  refine ⟨43526089707095376032709899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116069572552254336087226397 43526089707095376032709899)
  ·
    refine ⟨65289134560643064049064849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43526089707095376032709899 65289134560643064049064849)
    ·
      refine ⟨48966850920482298036798637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65289134560643064049064849 48966850920482298036798637)
      ·
        refine ⟨18362569095180861763799489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48966850920482298036798637 18362569095180861763799489)
        ·
          refine ⟨13771926821385646322849617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18362569095180861763799489 13771926821385646322849617)
          ·
            refine ⟨10328945116039234742137213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13771926821385646322849617 10328945116039234742137213)
            ·
              refine ⟨3873354418514713028301455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10328945116039234742137213 3873354418514713028301455)
              ·
                refine ⟨5810031627772069542452183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3873354418514713028301455 5810031627772069542452183)
                ·
                  refine ⟨8715047441658104313678275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5810031627772069542452183 8715047441658104313678275)
                  ·
                    refine ⟨13072571162487156470517413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8715047441658104313678275 13072571162487156470517413)
                    ·
                      refine ⟨2451107092966341838222015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13072571162487156470517413 2451107092966341838222015)
                      ·
                        rfl

theorem cell23_4773514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_4773514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4773514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4773514 prefixEnd_4773514 := by exact prefixLift 4773514
  have htrace : WordTrace (prefixWord ++ tailWord_4773514) baseStart_4773514 baseEnd_4773514 := by
    simpa [prefixWord, tailWord_4773514, baseEnd_4773514] using wordTrace_append hprefix tailTrace_4773514
  have hstable : (prefixWord ++ tailWord_4773514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4773514).length < 2 ^ (prefixWord ++ tailWord_4773514).sum := by decide
  have hdescent : baseEnd_4773514 < baseStart_4773514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4773514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4773581 : List Nat := [1, 6, 2, 1, 1, 2, 1, 1, 4, 1, 3]
def baseStart_4773581 : Nat := 118140960795 + 4773581 * 2 ^ 59
def prefixEnd_4773581 : Nat := 4983230072969 + 3 ^ 40 * 4773581 * 2
def baseEnd_4773581 : Nat := 2451141496170193076084207

theorem tailTrace_4773581 : CollatzResearch.WordTrace tailWord_4773581 prefixEnd_4773581 2451141496170193076084207 := by
  unfold tailWord_4773581
  simp only [CollatzResearch.WordTrace]
  refine ⟨174106802519138774573528597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116071201679425849715685731 174106802519138774573528597)
  ·
    refine ⟨8161256368084630058134153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 174106802519138774573528597 8161256368084630058134153)
    ·
      refine ⟨6120942276063472543600615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8161256368084630058134153 6120942276063472543600615)
      ·
        refine ⟨9181413414095208815400923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6120942276063472543600615 9181413414095208815400923)
        ·
          refine ⟨13772120121142813223101385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9181413414095208815400923 13772120121142813223101385)
          ·
            refine ⟨10329090090857109917326039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13772120121142813223101385 10329090090857109917326039)
            ·
              refine ⟨15493635136285664875989059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10329090090857109917326039 15493635136285664875989059)
              ·
                refine ⟨23240452704428497313983589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15493635136285664875989059 23240452704428497313983589)
                ·
                  refine ⟨4357584882080343246371923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23240452704428497313983589 4357584882080343246371923)
                  ·
                    refine ⟨6536377323120514869557885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4357584882080343246371923 6536377323120514869557885)
                    ·
                      refine ⟨2451141496170193076084207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6536377323120514869557885 2451141496170193076084207)
                      ·
                        rfl

theorem cell23_4773581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_4773581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4773581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4773581 prefixEnd_4773581 := by exact prefixLift 4773581
  have htrace : WordTrace (prefixWord ++ tailWord_4773581) baseStart_4773581 baseEnd_4773581 := by
    simpa [prefixWord, tailWord_4773581, baseEnd_4773581] using wordTrace_append hprefix tailTrace_4773581
  have hstable : (prefixWord ++ tailWord_4773581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4773581).length < 2 ^ (prefixWord ++ tailWord_4773581).sum := by decide
  have hdescent : baseEnd_4773581 < baseStart_4773581 := by decide
  rcases family_descends (prefixWord ++ tailWord_4773581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4773600 : List Nat := [2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 4]
def baseStart_4773600 : Nat := 118140960795 + 4773600 * 2 ^ 59
def prefixEnd_4773600 : Nat := 4983230072969 + 3 ^ 40 * 4773600 * 2
def baseEnd_4773600 : Nat := 2451151252302628501746619

theorem tailTrace_4773600 : CollatzResearch.WordTrace tailWord_4773600 prefixEnd_4773600 2451151252302628501746619 := by
  unfold tailWord_4773600
  simp only [CollatzResearch.WordTrace]
  refine ⟨87053747753034970409235127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116071663670713293878980169 87053747753034970409235127)
  ·
    refine ⟨130580621629552455613852691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87053747753034970409235127 130580621629552455613852691)
    ·
      refine ⟨195870932444328683420779037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130580621629552455613852691 195870932444328683420779037)
      ·
        refine ⟨73451599666623256282792139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195870932444328683420779037 73451599666623256282792139)
        ·
          refine ⟨110177399499934884424188209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73451599666623256282792139 110177399499934884424188209)
          ·
            refine ⟨82633049624951163318141157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110177399499934884424188209 82633049624951163318141157)
            ·
              refine ⟨15493696804678343122151467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82633049624951163318141157 15493696804678343122151467)
              ·
                refine ⟨23240545207017514683227201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15493696804678343122151467 23240545207017514683227201)
                ·
                  refine ⟨17430408905263136012420401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23240545207017514683227201 17430408905263136012420401)
                  ·
                    refine ⟨13072806678947352009315301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17430408905263136012420401 13072806678947352009315301)
                    ·
                      refine ⟨2451151252302628501746619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13072806678947352009315301 2451151252302628501746619)
                      ·
                        rfl

theorem cell23_4773600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_4773600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4773600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4773600 prefixEnd_4773600 := by exact prefixLift 4773600
  have htrace : WordTrace (prefixWord ++ tailWord_4773600) baseStart_4773600 baseEnd_4773600 := by
    simpa [prefixWord, tailWord_4773600, baseEnd_4773600] using wordTrace_append hprefix tailTrace_4773600
  have hstable : (prefixWord ++ tailWord_4773600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4773600).length < 2 ^ (prefixWord ++ tailWord_4773600).sum := by decide
  have hdescent : baseEnd_4773600 < baseStart_4773600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4773600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4773610 : List Nat := [3, 1, 3, 1, 1, 1, 4, 2, 7]
def baseStart_4773610 : Nat := 118140960795 + 4773610 * 2 ^ 59
def prefixEnd_4773610 : Nat := 4983230072969 + 3 ^ 40 * 4773610 * 2
def baseEnd_4773610 : Nat := 272350709678797051402397

theorem tailTrace_4773610 : CollatzResearch.WordTrace tailWord_4773610 prefixEnd_4773610 272350709678797051402397 := by
  unfold tailWord_4773610
  simp only [CollatzResearch.WordTrace]
  refine ⟨43526965059008428131583571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116071906824022475017556189 43526965059008428131583571)
  ·
    refine ⟨65290447588512642197375357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43526965059008428131583571 65290447588512642197375357)
    ·
      refine ⟨24483917845692240824015759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65290447588512642197375357 24483917845692240824015759)
      ·
        refine ⟨36725876768538361236023639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24483917845692240824015759 36725876768538361236023639)
        ·
          refine ⟨55088815152807541854035459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36725876768538361236023639 55088815152807541854035459)
          ·
            refine ⟨82633222729211312781053189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55088815152807541854035459 82633222729211312781053189)
            ·
              refine ⟨15493729261727121146447473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82633222729211312781053189 15493729261727121146447473)
              ·
                refine ⟨11620296946295340859835605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15493729261727121146447473 11620296946295340859835605)
                ·
                  refine ⟨272350709678797051402397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11620296946295340859835605 272350709678797051402397)
                  ·
                    rfl

theorem cell23_4773610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 7].length) (baseStart_4773610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4773610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4773610 prefixEnd_4773610 := by exact prefixLift 4773610
  have htrace : WordTrace (prefixWord ++ tailWord_4773610) baseStart_4773610 baseEnd_4773610 := by
    simpa [prefixWord, tailWord_4773610, baseEnd_4773610] using wordTrace_append hprefix tailTrace_4773610
  have hstable : (prefixWord ++ tailWord_4773610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4773610).length < 2 ^ (prefixWord ++ tailWord_4773610).sum := by decide
  have hdescent : baseEnd_4773610 < baseStart_4773610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4773610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4773694 : List Nat := [4, 2, 1, 2, 2, 1, 2, 2, 2, 1, 4]
def baseStart_4773694 : Nat := 118140960795 + 4773694 * 2 ^ 59
def prefixEnd_4773694 : Nat := 4983230072969 + 3 ^ 40 * 4773694 * 2
def baseEnd_4773694 : Nat := 2451199519484151133971187

theorem tailTrace_4773694 : CollatzResearch.WordTrace tailWord_4773694 prefixEnd_4773694 2451199519484151133971187 := by
  unfold tailWord_4773694
  simp only [CollatzResearch.WordTrace]
  refine ⟨21763865495966174359049017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116073949311819596581594757 21763865495966174359049017)
  ·
    refine ⟨16322899121974630769286763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21763865495966174359049017 16322899121974630769286763)
    ·
      refine ⟨24484348682961946153930145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16322899121974630769286763 24484348682961946153930145)
      ·
        refine ⟨18363261512221459615447609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24484348682961946153930145 18363261512221459615447609)
        ·
          refine ⟨13772446134166094711585707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18363261512221459615447609 13772446134166094711585707)
          ·
            refine ⟨20658669201249142067378561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13772446134166094711585707 20658669201249142067378561)
            ·
              refine ⟨15494001900936856550533921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20658669201249142067378561 15494001900936856550533921)
              ·
                refine ⟨11620501425702642412900441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15494001900936856550533921 11620501425702642412900441)
                ·
                  refine ⟨8715376069276981809675331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11620501425702642412900441 8715376069276981809675331)
                  ·
                    refine ⟨13073064103915472714512997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8715376069276981809675331 13073064103915472714512997)
                    ·
                      refine ⟨2451199519484151133971187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13073064103915472714512997 2451199519484151133971187)
                      ·
                        rfl

theorem cell23_4773694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_4773694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4773694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4773694 prefixEnd_4773694 := by exact prefixLift 4773694
  have htrace : WordTrace (prefixWord ++ tailWord_4773694) baseStart_4773694 baseEnd_4773694 := by
    simpa [prefixWord, tailWord_4773694, baseEnd_4773694] using wordTrace_append hprefix tailTrace_4773694
  have hstable : (prefixWord ++ tailWord_4773694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4773694).length < 2 ^ (prefixWord ++ tailWord_4773694).sum := by decide
  have hdescent : baseEnd_4773694 < baseStart_4773694 := by decide
  rcases family_descends (prefixWord ++ tailWord_4773694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4773717 : List Nat := [1, 3, 2, 2, 2, 2, 2, 3, 6]
def baseStart_4773717 : Nat := 118140960795 + 4773717 * 2 ^ 59
def prefixEnd_4773717 : Nat := 4983230072969 + 3 ^ 40 * 4773717 * 2
def baseEnd_4773717 : Nat := 272356814393244949331509

theorem tailTrace_4773717 : CollatzResearch.WordTrace tailWord_4773717 prefixEnd_4773717 272356814393244949331509 := by
  unfold tailWord_4773717
  simp only [CollatzResearch.WordTrace]
  refine ⟨174111762846646069800479405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116074508564430713200319603 174111762846646069800479405)
  ·
    refine ⟨65291911067492276175179777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174111762846646069800479405 65291911067492276175179777)
    ·
      refine ⟨48968933300619207131384833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65291911067492276175179777 48968933300619207131384833)
      ·
        refine ⟨36726699975464405348538625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48968933300619207131384833 36726699975464405348538625)
        ·
          refine ⟨27545024981598304011403969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36726699975464405348538625 27545024981598304011403969)
          ·
            refine ⟨20658768736198728008552977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27545024981598304011403969 20658768736198728008552977)
            ·
              refine ⟨15494076552149046006414733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20658768736198728008552977 15494076552149046006414733)
              ·
                refine ⟨5810278707055892252405525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15494076552149046006414733 5810278707055892252405525)
                ·
                  refine ⟨272356814393244949331509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5810278707055892252405525 272356814393244949331509)
                  ·
                    rfl

theorem cell23_4773717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 3, 6].length) (baseStart_4773717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4773717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4773717 prefixEnd_4773717 := by exact prefixLift 4773717
  have htrace : WordTrace (prefixWord ++ tailWord_4773717) baseStart_4773717 baseEnd_4773717 := by
    simpa [prefixWord, tailWord_4773717, baseEnd_4773717] using wordTrace_append hprefix tailTrace_4773717
  have hstable : (prefixWord ++ tailWord_4773717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4773717).length < 2 ^ (prefixWord ++ tailWord_4773717).sum := by decide
  have hdescent : baseEnd_4773717 < baseStart_4773717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4773717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4773731 : List Nat := [1, 1, 1, 5, 4, 2, 1, 1, 2, 2, 3]
def baseStart_4773731 : Nat := 118140960795 + 4773731 * 2 ^ 59
def prefixEnd_4773731 : Nat := 4983230072969 + 3 ^ 40 * 4773731 * 2
def baseEnd_4773731 : Nat := 2451218518268367489208517

theorem tailTrace_4773731 : CollatzResearch.WordTrace tailWord_4773731 prefixEnd_4773731 2451218518268367489208517 := by
  unfold tailWord_4773731
  simp only [CollatzResearch.WordTrace]
  refine ⟨174112273468595350191489047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116074848979063566794326031 174112273468595350191489047)
  ·
    refine ⟨261168410202893025287233571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174112273468595350191489047 261168410202893025287233571)
    ·
      refine ⟨391752615304339537930850357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261168410202893025287233571 391752615304339537930850357)
      ·
        refine ⟨36726807684781831681017221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 391752615304339537930850357 36726807684781831681017221)
        ·
          refine ⟨6886276440896593440190729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36726807684781831681017221 6886276440896593440190729)
          ·
            refine ⟨5164707330672445080143047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6886276440896593440190729 5164707330672445080143047)
            ·
              refine ⟨7747060996008667620214571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5164707330672445080143047 7747060996008667620214571)
              ·
                refine ⟨11620591494013001430321857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7747060996008667620214571 11620591494013001430321857)
                ·
                  refine ⟨8715443620509751072741393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11620591494013001430321857 8715443620509751072741393)
                  ·
                    refine ⟨6536582715382313304556045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8715443620509751072741393 6536582715382313304556045)
                    ·
                      refine ⟨2451218518268367489208517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6536582715382313304556045 2451218518268367489208517)
                      ·
                        rfl

theorem cell23_4773731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_4773731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4773731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4773731 prefixEnd_4773731 := by exact prefixLift 4773731
  have htrace : WordTrace (prefixWord ++ tailWord_4773731) baseStart_4773731 baseEnd_4773731 := by
    simpa [prefixWord, tailWord_4773731, baseEnd_4773731] using wordTrace_append hprefix tailTrace_4773731
  have hstable : (prefixWord ++ tailWord_4773731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4773731).length < 2 ^ (prefixWord ++ tailWord_4773731).sum := by decide
  have hdescent : baseEnd_4773731 < baseStart_4773731 := by decide
  rcases family_descends (prefixWord ++ tailWord_4773731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4773754 : List Nat := [3, 1, 1, 1, 1, 1, 4, 4, 2, 3, 2]
def baseStart_4773754 : Nat := 118140960795 + 4773754 * 2 ^ 59
def prefixEnd_4773754 : Nat := 4983230072969 + 3 ^ 40 * 4773754 * 2
def baseEnd_4773754 : Nat := 2451230328323420899220911

theorem tailTrace_4773754 : CollatzResearch.WordTrace tailWord_4773754 prefixEnd_4773754 2451230328323420899220911 := by
  unfold tailWord_4773754
  simp only [CollatzResearch.WordTrace]
  refine ⟨43528278086878006279894079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116075408231674683413050877 43528278086878006279894079)
  ·
    refine ⟨65292417130317009419841119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43528278086878006279894079 65292417130317009419841119)
    ·
      refine ⟨97938625695475514129761679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65292417130317009419841119 97938625695475514129761679)
      ·
        refine ⟨146907938543213271194642519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97938625695475514129761679 146907938543213271194642519)
        ·
          refine ⟨220361907814819906791963779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146907938543213271194642519 220361907814819906791963779)
          ·
            refine ⟨330542861722229860187945669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220361907814819906791963779 330542861722229860187945669)
            ·
              refine ⟨61976786572918098785239813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 330542861722229860187945669 61976786572918098785239813)
              ·
                refine ⟨11620647482422143522232465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61976786572918098785239813 11620647482422143522232465)
                ·
                  refine ⟨8715485611816607641674349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11620647482422143522232465 8715485611816607641674349)
                  ·
                    refine ⟨3268307104431227865627881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8715485611816607641674349 3268307104431227865627881)
                    ·
                      refine ⟨2451230328323420899220911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3268307104431227865627881 2451230328323420899220911)
                      ·
                        rfl

theorem cell23_4773754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 2, 3, 2].length) (baseStart_4773754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4773754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4773754 prefixEnd_4773754 := by exact prefixLift 4773754
  have htrace : WordTrace (prefixWord ++ tailWord_4773754) baseStart_4773754 baseEnd_4773754 := by
    simpa [prefixWord, tailWord_4773754, baseEnd_4773754] using wordTrace_append hprefix tailTrace_4773754
  have hstable : (prefixWord ++ tailWord_4773754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4773754).length < 2 ^ (prefixWord ++ tailWord_4773754).sum := by decide
  have hdescent : baseEnd_4773754 < baseStart_4773754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4773754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4773777 : List Nat := [1, 2, 2, 1, 1, 1, 7, 1, 1, 6]
def baseStart_4773777 : Nat := 118140960795 + 4773777 * 2 ^ 59
def prefixEnd_4773777 : Nat := 4983230072969 + 3 ^ 40 * 4773777 * 2
def baseEnd_4773777 : Nat := 817080712792824769744435

theorem tailTrace_4773777 : CollatzResearch.WordTrace tailWord_4773777 prefixEnd_4773777 817080712792824769744435 := by
  unfold tailWord_4773777
  simp only [CollatzResearch.WordTrace]
  refine ⟨174113951226428700047663585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116075967484285800031775723 174113951226428700047663585)
  ·
    refine ⟨130585463419821525035747689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174113951226428700047663585 130585463419821525035747689)
    ·
      refine ⟨97939097564866143776810767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130585463419821525035747689 97939097564866143776810767)
      ·
        refine ⟨146908646347299215665216151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97939097564866143776810767 146908646347299215665216151)
        ·
          refine ⟨220362969520948823497824227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146908646347299215665216151 220362969520948823497824227)
          ·
            refine ⟨330544454281423235246736341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220362969520948823497824227 330544454281423235246736341)
            ·
              refine ⟨7747135647220857076095383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 330544454281423235246736341 7747135647220857076095383)
              ·
                refine ⟨11620703470831285614143075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7747135647220857076095383 11620703470831285614143075)
                ·
                  refine ⟨17431055206246928421214613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11620703470831285614143075 17431055206246928421214613)
                  ·
                    refine ⟨817080712792824769744435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17431055206246928421214613 817080712792824769744435)
                    ·
                      rfl

theorem cell23_4773777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 6].length) (baseStart_4773777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4773777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4773777 prefixEnd_4773777 := by exact prefixLift 4773777
  have htrace : WordTrace (prefixWord ++ tailWord_4773777) baseStart_4773777 baseEnd_4773777 := by
    simpa [prefixWord, tailWord_4773777, baseEnd_4773777] using wordTrace_append hprefix tailTrace_4773777
  have hstable : (prefixWord ++ tailWord_4773777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4773777).length < 2 ^ (prefixWord ++ tailWord_4773777).sum := by decide
  have hdescent : baseEnd_4773777 < baseStart_4773777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4773777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4773797 : List Nat := [1, 3, 1, 2, 1, 1, 1, 6, 1, 2, 4]
def baseStart_4773797 : Nat := 118140960795 + 4773797 * 2 ^ 59
def prefixEnd_4773797 : Nat := 4983230072969 + 3 ^ 40 * 4773797 * 2
def baseEnd_4773797 : Nat := 2451252407991564230983213

theorem tailTrace_4773797 : CollatzResearch.WordTrace tailWord_4773797 prefixEnd_4773797 2451252407991564230983213 := by
  unfold tailWord_4773797
  simp only [CollatzResearch.WordTrace]
  refine ⟨174114680686356243463391645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116076453790904162308927763 174114680686356243463391645)
  ·
    refine ⟨65293005257383591298771867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174114680686356243463391645 65293005257383591298771867)
    ·
      refine ⟨97939507886075386948157801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65293005257383591298771867 97939507886075386948157801)
      ·
        refine ⟨73454630914556540211118351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97939507886075386948157801 73454630914556540211118351)
        ·
          refine ⟨110181946371834810316677527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73454630914556540211118351 110181946371834810316677527)
          ·
            refine ⟨165272919557752215475016291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110181946371834810316677527 165272919557752215475016291)
            ·
              refine ⟨247909379336628323212524437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165272919557752215475016291 247909379336628323212524437)
              ·
                refine ⟨11620752156404452650587083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 247909379336628323212524437 11620752156404452650587083)
                ·
                  refine ⟨17431128234606678975880625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11620752156404452650587083 17431128234606678975880625)
                  ·
                    refine ⟨13073346175955009231910469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17431128234606678975880625 13073346175955009231910469)
                    ·
                      refine ⟨2451252407991564230983213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13073346175955009231910469 2451252407991564230983213)
                      ·
                        rfl

theorem cell23_4773797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_4773797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4773797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4773797 prefixEnd_4773797 := by exact prefixLift 4773797
  have htrace : WordTrace (prefixWord ++ tailWord_4773797) baseStart_4773797 baseEnd_4773797 := by
    simpa [prefixWord, tailWord_4773797, baseEnd_4773797] using wordTrace_append hprefix tailTrace_4773797
  have hstable : (prefixWord ++ tailWord_4773797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4773797).length < 2 ^ (prefixWord ++ tailWord_4773797).sum := by decide
  have hdescent : baseEnd_4773797 < baseStart_4773797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4773797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4773812 : List Nat := [2, 5, 2, 1, 3, 1, 1, 1, 3, 1, 3]
def baseStart_4773812 : Nat := 118140960795 + 4773812 * 2 ^ 59
def prefixEnd_4773812 : Nat := 4983230072969 + 3 ^ 40 * 4773812 * 2
def baseEnd_4773812 : Nat := 2451260110201381672295645

theorem tailTrace_4773812 : CollatzResearch.WordTrace tailWord_4773812 prefixEnd_4773812 2451260110201381672295645 := by
  unfold tailWord_4773812
  simp only [CollatzResearch.WordTrace]
  refine ⟨87057613890650950512593845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116076818520867934016791793 87057613890650950512593845)
  ·
    refine ⟨8161651302248526610555673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87057613890650950512593845 8161651302248526610555673)
    ·
      refine ⟨6121238476686394957916755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8161651302248526610555673 6121238476686394957916755)
      ·
        refine ⟨9181857715029592436875133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6121238476686394957916755 9181857715029592436875133)
        ·
          refine ⟨3443196643136097163828175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9181857715029592436875133 3443196643136097163828175)
          ·
            refine ⟨5164794964704145745742263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3443196643136097163828175 5164794964704145745742263)
            ·
              refine ⟨7747192447056218618613395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5164794964704145745742263 7747192447056218618613395)
              ·
                refine ⟨11620788670584327927920093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7747192447056218618613395 11620788670584327927920093)
                ·
                  refine ⟨4357795751469122972970035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11620788670584327927920093 4357795751469122972970035)
                  ·
                    refine ⟨6536693627203684459455053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4357795751469122972970035 6536693627203684459455053)
                    ·
                      refine ⟨2451260110201381672295645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6536693627203684459455053 2451260110201381672295645)
                      ·
                        rfl

theorem cell23_4773812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_4773812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4773812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4773812 prefixEnd_4773812 := by exact prefixLift 4773812
  have htrace : WordTrace (prefixWord ++ tailWord_4773812) baseStart_4773812 baseEnd_4773812 := by
    simpa [prefixWord, tailWord_4773812, baseEnd_4773812] using wordTrace_append hprefix tailTrace_4773812
  have hstable : (prefixWord ++ tailWord_4773812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4773812).length < 2 ^ (prefixWord ++ tailWord_4773812).sum := by decide
  have hdescent : baseEnd_4773812 < baseStart_4773812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4773812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4773852 : List Nat := [2, 2, 6, 1, 1, 1, 3, 1, 1, 1, 4]
def baseStart_4773852 : Nat := 118140960795 + 4773852 * 2 ^ 59
def prefixEnd_4773852 : Nat := 4983230072969 + 3 ^ 40 * 4773852 * 2
def baseEnd_4773852 : Nat := 2451280649427561515795461

theorem tailTrace_4773852 : CollatzResearch.WordTrace tailWord_4773852 prefixEnd_4773852 2451280649427561515795461 := by
  unfold tailWord_4773852
  simp only [CollatzResearch.WordTrace]
  refine ⟨87058343350578493928321905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116077791134104658571095873 87058343350578493928321905)
  ·
    refine ⟨65293757512933870446241429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87058343350578493928321905 65293757512933870446241429)
    ·
      refine ⟨3060644883418775177167567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 65293757512933870446241429 3060644883418775177167567)
      ·
        refine ⟨4590967325128162765751351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3060644883418775177167567 4590967325128162765751351)
        ·
          refine ⟨6886450987692244148627027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4590967325128162765751351 6886450987692244148627027)
          ·
            refine ⟨10329676481538366222940541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6886450987692244148627027 10329676481538366222940541)
            ·
              refine ⟨3873628680576887333602703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10329676481538366222940541 3873628680576887333602703)
              ·
                refine ⟨5810443020865331000404055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3873628680576887333602703 5810443020865331000404055)
                ·
                  refine ⟨8715664531297996500606083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5810443020865331000404055 8715664531297996500606083)
                  ·
                    refine ⟨13073496796946994750909125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8715664531297996500606083 13073496796946994750909125)
                    ·
                      refine ⟨2451280649427561515795461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13073496796946994750909125 2451280649427561515795461)
                      ·
                        rfl

theorem cell23_4773852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_4773852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4773852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4773852 prefixEnd_4773852 := by exact prefixLift 4773852
  have htrace : WordTrace (prefixWord ++ tailWord_4773852) baseStart_4773852 baseEnd_4773852 := by
    simpa [prefixWord, tailWord_4773852, baseEnd_4773852] using wordTrace_append hprefix tailTrace_4773852
  have hstable : (prefixWord ++ tailWord_4773852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4773852).length < 2 ^ (prefixWord ++ tailWord_4773852).sum := by decide
  have hdescent : baseEnd_4773852 < baseStart_4773852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4773852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4773925 : List Nat := [1, 3, 1, 2, 2, 5, 1, 2, 2, 2, 2]
def baseStart_4773925 : Nat := 118140960795 + 4773925 * 2 ^ 59
def prefixEnd_4773925 : Nat := 4983230072969 + 3 ^ 40 * 4773925 * 2
def baseEnd_4773925 : Nat := 2451318133515339730182625

theorem tailTrace_4773925 : CollatzResearch.WordTrace tailWord_4773925 prefixEnd_4773925 2451318133515339730182625 := by
  unfold tailWord_4773925
  simp only [CollatzResearch.WordTrace]
  refine ⟨174119349229892521324051229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116079566153261680882700819 174119349229892521324051229)
  ·
    refine ⟨65294755961209695496519211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174119349229892521324051229 65294755961209695496519211)
    ·
      refine ⟨97942133941814543244778817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65294755961209695496519211 97942133941814543244778817)
      ·
        refine ⟨73456600456360907433584113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97942133941814543244778817 73456600456360907433584113)
        ·
          refine ⟨55092450342270680575188085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73456600456360907433584113 55092450342270680575188085)
          ·
            refine ⟨5164917219587876303923883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55092450342270680575188085 5164917219587876303923883)
            ·
              refine ⟨7747375829381814455885825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5164917219587876303923883 7747375829381814455885825)
              ·
                refine ⟨5810531872036360841914369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7747375829381814455885825 5810531872036360841914369)
                ·
                  refine ⟨4357898904027270631435777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5810531872036360841914369 4357898904027270631435777)
                  ·
                    refine ⟨3268424178020452973576833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4357898904027270631435777 3268424178020452973576833)
                    ·
                      refine ⟨2451318133515339730182625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3268424178020452973576833 2451318133515339730182625)
                      ·
                        rfl

theorem cell23_4773925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 2, 2, 2, 2].length) (baseStart_4773925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4773925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4773925 prefixEnd_4773925 := by exact prefixLift 4773925
  have htrace : WordTrace (prefixWord ++ tailWord_4773925) baseStart_4773925 baseEnd_4773925 := by
    simpa [prefixWord, tailWord_4773925, baseEnd_4773925] using wordTrace_append hprefix tailTrace_4773925
  have hstable : (prefixWord ++ tailWord_4773925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4773925).length < 2 ^ (prefixWord ++ tailWord_4773925).sum := by decide
  have hdescent : baseEnd_4773925 < baseStart_4773925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4773925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4773942 : List Nat := [5, 1, 2, 1, 1, 1, 5, 1, 2, 2, 2]
def baseStart_4773942 : Nat := 118140960795 + 4773942 * 2 ^ 59
def prefixEnd_4773942 : Nat := 4983230072969 + 3 ^ 40 * 4773942 * 2
def baseEnd_4773942 : Nat := 2451326862686466163670047

theorem tailTrace_4773942 : CollatzResearch.WordTrace tailWord_4773942 prefixEnd_4773942 2451326862686466163670047 := by
  unfold tailWord_4773942
  simp only [CollatzResearch.WordTrace]
  refine ⟨10882498079426933326713755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116079979513887288818280053 10882498079426933326713755)
  ·
    refine ⟨16323747119140399990070633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10882498079426933326713755 16323747119140399990070633)
    ·
      refine ⟨12242810339355299992552975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16323747119140399990070633 12242810339355299992552975)
      ·
        refine ⟨18364215509032949988829463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12242810339355299992552975 18364215509032949988829463)
        ·
          refine ⟨27546323263549424983244195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18364215509032949988829463 27546323263549424983244195)
          ·
            refine ⟨41319484895324137474866293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27546323263549424983244195 41319484895324137474866293)
            ·
              refine ⟨3873701708936637888268715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41319484895324137474866293 3873701708936637888268715)
              ·
                refine ⟨5810552563404956832403073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3873701708936637888268715 5810552563404956832403073)
                ·
                  refine ⟨4357914422553717624302305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5810552563404956832403073 4357914422553717624302305)
                  ·
                    refine ⟨3268435816915288218226729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4357914422553717624302305 3268435816915288218226729)
                    ·
                      refine ⟨2451326862686466163670047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3268435816915288218226729 2451326862686466163670047)
                      ·
                        rfl

theorem cell23_4773942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_4773942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4773942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4773942 prefixEnd_4773942 := by exact prefixLift 4773942
  have htrace : WordTrace (prefixWord ++ tailWord_4773942) baseStart_4773942 baseEnd_4773942 := by
    simpa [prefixWord, tailWord_4773942, baseEnd_4773942] using wordTrace_append hprefix tailTrace_4773942
  have hstable : (prefixWord ++ tailWord_4773942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4773942).length < 2 ^ (prefixWord ++ tailWord_4773942).sum := by decide
  have hdescent : baseEnd_4773942 < baseStart_4773942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4773942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4773957 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 1, 10]
def baseStart_4773957 : Nat := 118140960795 + 4773957 * 2 ^ 59
def prefixEnd_4773957 : Nat := 4983230072969 + 3 ^ 40 * 4773957 * 2
def baseEnd_4773957 : Nat := 817111521632094534994159

theorem tailTrace_4773957 : CollatzResearch.WordTrace tailWord_4773957 prefixEnd_4773957 817111521632094534994159 := by
  unfold tailWord_4773957
  simp only [CollatzResearch.WordTrace]
  refine ⟨174120516365776590789216125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116080344243851060526144083 174120516365776590789216125)
  ·
    refine ⟨65295193637166221545956047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174120516365776590789216125 65295193637166221545956047)
    ·
      refine ⟨97942790455749332318934071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65295193637166221545956047 97942790455749332318934071)
      ·
        refine ⟨146914185683623998478401107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97942790455749332318934071 146914185683623998478401107)
        ·
          refine ⟨220371278525435997717601661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146914185683623998478401107 220371278525435997717601661)
          ·
            refine ⟨82639229447038499144100623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 220371278525435997717601661 82639229447038499144100623)
            ·
              refine ⟨123958844170557748716150935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82639229447038499144100623 123958844170557748716150935)
              ·
                refine ⟨185938266255836623074226403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123958844170557748716150935 185938266255836623074226403)
                ·
                  refine ⟨278907399383754934611339605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 185938266255836623074226403 278907399383754934611339605)
                  ·
                    refine ⟨817111521632094534994159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 278907399383754934611339605 817111521632094534994159)
                    ·
                      rfl

theorem cell23_4773957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 10].length) (baseStart_4773957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4773957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4773957 prefixEnd_4773957 := by exact prefixLift 4773957
  have htrace : WordTrace (prefixWord ++ tailWord_4773957) baseStart_4773957 baseEnd_4773957 := by
    simpa [prefixWord, tailWord_4773957, baseEnd_4773957] using wordTrace_append hprefix tailTrace_4773957
  have hstable : (prefixWord ++ tailWord_4773957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4773957).length < 2 ^ (prefixWord ++ tailWord_4773957).sum := by decide
  have hdescent : baseEnd_4773957 < baseStart_4773957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4773957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4773964 : List Nat := [2, 2, 1, 3, 1, 1, 4, 1, 1, 3, 4]
def baseStart_4773964 : Nat := 118140960795 + 4773964 * 2 ^ 59
def prefixEnd_4773964 : Nat := 4983230072969 + 3 ^ 40 * 4773964 * 2
def baseEnd_4773964 : Nat := 2451338159260865077594945

theorem tailTrace_4773964 : CollatzResearch.WordTrace tailWord_4773964 prefixEnd_4773964 2451338159260865077594945 := by
  unfold tailWord_4773964
  simp only [CollatzResearch.WordTrace]
  refine ⟨87060385838375615492360473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116080514451167487323147297 87060385838375615492360473)
  ·
    refine ⟨65295289378781711619270355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87060385838375615492360473 65295289378781711619270355)
    ·
      refine ⟨97942934068172567428905533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65295289378781711619270355 97942934068172567428905533)
      ·
        refine ⟨36728600275564712785839575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97942934068172567428905533 36728600275564712785839575)
        ·
          refine ⟨55092900413347069178759363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36728600275564712785839575 55092900413347069178759363)
          ·
            refine ⟨82639350620020603768139045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55092900413347069178759363 82639350620020603768139045)
            ·
              refine ⟨15494878241253863206526071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82639350620020603768139045 15494878241253863206526071)
              ·
                refine ⟨23242317361880794809789107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15494878241253863206526071 23242317361880794809789107)
                ·
                  refine ⟨34863476042821192214683661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23242317361880794809789107 34863476042821192214683661)
                  ·
                    refine ⟨13073803516057947080506373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34863476042821192214683661 13073803516057947080506373)
                    ·
                      refine ⟨2451338159260865077594945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13073803516057947080506373 2451338159260865077594945)
                      ·
                        rfl

theorem cell23_4773964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_4773964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4773964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4773964 prefixEnd_4773964 := by exact prefixLift 4773964
  have htrace : WordTrace (prefixWord ++ tailWord_4773964) baseStart_4773964 baseEnd_4773964 := by
    simpa [prefixWord, tailWord_4773964, baseEnd_4773964] using wordTrace_append hprefix tailTrace_4773964
  have hstable : (prefixWord ++ tailWord_4773964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4773964).length < 2 ^ (prefixWord ++ tailWord_4773964).sum := by decide
  have hdescent : baseEnd_4773964 < baseStart_4773964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4773964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4773982 : List Nat := [4, 4, 1, 1, 3, 1, 1, 1, 7]
def baseStart_4773982 : Nat := 118140960795 + 4773982 * 2 ^ 59
def prefixEnd_4773982 : Nat := 4983230072969 + 3 ^ 40 * 4773982 * 2
def baseEnd_4773982 : Nat := 272371933545849556352207

theorem tailTrace_4773982 : CollatzResearch.WordTrace tailWord_4773982 prefixEnd_4773982 272371933545849556352207 := by
  unfold tailWord_4773982
  simp only [CollatzResearch.WordTrace]
  refine ⟨21765178523835752507359525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116080952127124013372584133 21765178523835752507359525)
  ·
    refine ⟨4080970973219203595129911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21765178523835752507359525 4080970973219203595129911)
    ·
      refine ⟨6121456459828805392694867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4080970973219203595129911 6121456459828805392694867)
      ·
        refine ⟨9182184689743208089042301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6121456459828805392694867 9182184689743208089042301)
        ·
          refine ⟨3443319258653703033390863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9182184689743208089042301 3443319258653703033390863)
          ·
            refine ⟨5164978887980554550086295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3443319258653703033390863 5164978887980554550086295)
            ·
              refine ⟨7747468331970831825129443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5164978887980554550086295 7747468331970831825129443)
              ·
                refine ⟨11621202497956247737694165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7747468331970831825129443 11621202497956247737694165)
                ·
                  refine ⟨272371933545849556352207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11621202497956247737694165 272371933545849556352207)
                  ·
                    rfl

theorem cell23_4773982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_4773982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4773982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4773982 prefixEnd_4773982 := by exact prefixLift 4773982
  have htrace : WordTrace (prefixWord ++ tailWord_4773982) baseStart_4773982 baseEnd_4773982 := by
    simpa [prefixWord, tailWord_4773982, baseEnd_4773982] using wordTrace_append hprefix tailTrace_4773982
  have hstable : (prefixWord ++ tailWord_4773982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4773982).length < 2 ^ (prefixWord ++ tailWord_4773982).sum := by decide
  have hdescent : baseEnd_4773982 < baseStart_4773982 := by decide
  rcases family_descends (prefixWord ++ tailWord_4773982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774065 : List Nat := [1, 2, 2, 5, 2, 1, 1, 2, 3, 1, 3]
def baseStart_4774065 : Nat := 118140960795 + 4774065 * 2 ^ 59
def prefixEnd_4774065 : Nat := 4983230072969 + 3 ^ 40 * 4774065 * 2
def baseEnd_4774065 : Nat := 2451390020806969182431981

theorem tailTrace_4774065 : CollatzResearch.WordTrace tailWord_4774065 prefixEnd_4774065 2451390020806969182431981 := by
  unfold tailWord_4774065
  simp only [CollatzResearch.WordTrace]
  refine ⟨174124455449385325234147649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116082970299590216822765099 174124455449385325234147649)
  ·
    refine ⟨130593341587038993925610737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174124455449385325234147649 130593341587038993925610737)
    ·
      refine ⟨97945006190279245444208053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130593341587038993925610737 97945006190279245444208053)
      ·
        refine ⟨9182344330338679260394505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97945006190279245444208053 9182344330338679260394505)
        ·
          refine ⟨6886758247754009445295879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9182344330338679260394505 6886758247754009445295879)
          ·
            refine ⟨10330137371631014167943819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6886758247754009445295879 10330137371631014167943819)
            ·
              refine ⟨15495206057446521251915729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10330137371631014167943819 15495206057446521251915729)
              ·
                refine ⟨11621404543084890938936797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15495206057446521251915729 11621404543084890938936797)
                ·
                  refine ⟨4358026703656834102101299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11621404543084890938936797 4358026703656834102101299)
                  ·
                    refine ⟨6537040055485251153151949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4358026703656834102101299 6537040055485251153151949)
                    ·
                      refine ⟨2451390020806969182431981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6537040055485251153151949 2451390020806969182431981)
                      ·
                        rfl

theorem cell23_4774065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_4774065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774065 prefixEnd_4774065 := by exact prefixLift 4774065
  have htrace : WordTrace (prefixWord ++ tailWord_4774065) baseStart_4774065 baseEnd_4774065 := by
    simpa [prefixWord, tailWord_4774065, baseEnd_4774065] using wordTrace_append hprefix tailTrace_4774065
  have hstable : (prefixWord ++ tailWord_4774065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774065).length < 2 ^ (prefixWord ++ tailWord_4774065).sum := by decide
  have hdescent : baseEnd_4774065 < baseStart_4774065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774071 : List Nat := [1, 1, 3, 1, 4, 2, 2, 1, 3, 1, 4]
def baseStart_4774071 : Nat := 118140960795 + 4774071 * 2 ^ 59
def prefixEnd_4774071 : Nat := 4983230072969 + 3 ^ 40 * 4774071 * 2
def baseEnd_4774071 : Nat := 2451393101690896158956953

theorem tailTrace_4774071 : CollatzResearch.WordTrace tailWord_4774071 prefixEnd_4774071 2451393101690896158956953 := by
  unfold tailWord_4774071
  simp only [CollatzResearch.WordTrace]
  refine ⟨174124674287363588258866067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116083116191575725505910711 174124674287363588258866067)
  ·
    refine ⟨261187011431045382388299101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174124674287363588258866067 261187011431045382388299101)
    ·
      refine ⟨97945129286642018395612163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 261187011431045382388299101 97945129286642018395612163)
      ·
        refine ⟨146917693929963027593418245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97945129286642018395612163 146917693929963027593418245)
        ·
          refine ⟨27547067611868067673765921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 146917693929963027593418245 27547067611868067673765921)
          ·
            refine ⟨20660300708901050755324441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27547067611868067673765921 20660300708901050755324441)
            ·
              refine ⟨15495225531675788066493331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20660300708901050755324441 15495225531675788066493331)
              ·
                refine ⟨23242838297513682099739997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15495225531675788066493331 23242838297513682099739997)
                ·
                  refine ⟨8716064361567630787402499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23242838297513682099739997 8716064361567630787402499)
                  ·
                    refine ⟨13074096542351446181103749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8716064361567630787402499 13074096542351446181103749)
                    ·
                      refine ⟨2451393101690896158956953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13074096542351446181103749 2451393101690896158956953)
                      ·
                        rfl

theorem cell23_4774071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 3, 1, 4].length) (baseStart_4774071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774071 prefixEnd_4774071 := by exact prefixLift 4774071
  have htrace : WordTrace (prefixWord ++ tailWord_4774071) baseStart_4774071 baseEnd_4774071 := by
    simpa [prefixWord, tailWord_4774071, baseEnd_4774071] using wordTrace_append hprefix tailTrace_4774071
  have hstable : (prefixWord ++ tailWord_4774071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774071).length < 2 ^ (prefixWord ++ tailWord_4774071).sum := by decide
  have hdescent : baseEnd_4774071 < baseStart_4774071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774088 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 7, 2, 2]
def baseStart_4774088 : Nat := 118140960795 + 4774088 * 2 ^ 59
def prefixEnd_4774088 : Nat := 4983230072969 + 3 ^ 40 * 4774088 * 2
def baseEnd_4774088 : Nat := 2451401830862022592444375

theorem tailTrace_4774088 : CollatzResearch.WordTrace tailWord_4774088 prefixEnd_4774088 2451401830862022592444375 := by
  unfold tailWord_4774088
  simp only [CollatzResearch.WordTrace]
  refine ⟨87062647164151000081117459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116083529552201333441489945 87062647164151000081117459)
  ·
    refine ⟨130593970746226500121676189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87062647164151000081117459 130593970746226500121676189)
    ·
      refine ⟨48972739029834937545628571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130593970746226500121676189 48972739029834937545628571)
      ·
        refine ⟨73459108544752406318442857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48972739029834937545628571 73459108544752406318442857)
        ·
          refine ⟨55094331408564304738832143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73459108544752406318442857 55094331408564304738832143)
          ·
            refine ⟨82641497112846457108248215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55094331408564304738832143 82641497112846457108248215)
            ·
              refine ⟨123962245669269685662372323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82641497112846457108248215 123962245669269685662372323)
              ·
                refine ⟨185943368503904528493558485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123962245669269685662372323 185943368503904528493558485)
                ·
                  refine ⟨4358047699310262386567777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 185943368503904528493558485 4358047699310262386567777)
                  ·
                    refine ⟨3268535774482696789925833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4358047699310262386567777 3268535774482696789925833)
                    ·
                      refine ⟨2451401830862022592444375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3268535774482696789925833 2451401830862022592444375)
                      ·
                        rfl

theorem cell23_4774088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 7, 2, 2].length) (baseStart_4774088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774088 prefixEnd_4774088 := by exact prefixLift 4774088
  have htrace : WordTrace (prefixWord ++ tailWord_4774088) baseStart_4774088 baseEnd_4774088 := by
    simpa [prefixWord, tailWord_4774088, baseEnd_4774088] using wordTrace_append hprefix tailTrace_4774088
  have hstable : (prefixWord ++ tailWord_4774088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774088).length < 2 ^ (prefixWord ++ tailWord_4774088).sum := by decide
  have hdescent : baseEnd_4774088 < baseStart_4774088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774098 : List Nat := [3, 2, 2, 2, 1, 3, 1, 1, 4, 4]
def baseStart_4774098 : Nat := 118140960795 + 4774098 * 2 ^ 59
def prefixEnd_4774098 : Nat := 4983230072969 + 3 ^ 40 * 4774098 * 2
def baseEnd_4774098 : Nat := 817135655222855851106443

theorem tailTrace_4774098 : CollatzResearch.WordTrace tailWord_4774098 prefixEnd_4774098 817135655222855851106443 := by
  unfold tailWord_4774098
  simp only [CollatzResearch.WordTrace]
  refine ⟨43531414764566442967524737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116083772705510514580065965 43531414764566442967524737)
  ·
    refine ⟨32648561073424832225643553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43531414764566442967524737 32648561073424832225643553)
    ·
      refine ⟨24486420805068624169232665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32648561073424832225643553 24486420805068624169232665)
      ·
        refine ⟨18364815603801468126924499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24486420805068624169232665 18364815603801468126924499)
        ·
          refine ⟨27547223405702202190386749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18364815603801468126924499 27547223405702202190386749)
          ·
            refine ⟨10330208777138325821395031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27547223405702202190386749 10330208777138325821395031)
            ·
              refine ⟨15495313165707488732092547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10330208777138325821395031 15495313165707488732092547)
              ·
                refine ⟨23242969748561233098138821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15495313165707488732092547 23242969748561233098138821)
                ·
                  refine ⟨4358056827855231205901029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23242969748561233098138821 4358056827855231205901029)
                  ·
                    refine ⟨817135655222855851106443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4358056827855231205901029 817135655222855851106443)
                    ·
                      rfl

theorem cell23_4774098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_4774098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774098 prefixEnd_4774098 := by exact prefixLift 4774098
  have htrace : WordTrace (prefixWord ++ tailWord_4774098) baseStart_4774098 baseEnd_4774098 := by
    simpa [prefixWord, tailWord_4774098, baseEnd_4774098] using wordTrace_append hprefix tailTrace_4774098
  have hstable : (prefixWord ++ tailWord_4774098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774098).length < 2 ^ (prefixWord ++ tailWord_4774098).sum := by decide
  have hdescent : baseEnd_4774098 < baseStart_4774098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774115 : List Nat := [1, 1, 1, 8, 1, 2, 1, 1, 1, 6]
def baseStart_4774115 : Nat := 118140960795 + 4774115 * 2 ^ 59
def prefixEnd_4774115 : Nat := 4983230072969 + 3 ^ 40 * 4774115 * 2
def baseEnd_4774115 : Nat := 817138564946564662268917

theorem tailTrace_4774115 : CollatzResearch.WordTrace tailWord_4774115 prefixEnd_4774115 817138564946564662268917 := by
  unfold tailWord_4774115
  simp only [CollatzResearch.WordTrace]
  refine ⟨174126279099204183773467799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116084186066136122515645199 174126279099204183773467799)
  ·
    refine ⟨261189418648806275660201699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174126279099204183773467799 261189418648806275660201699)
    ·
      refine ⟨391784127973209413490302549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261189418648806275660201699 391784127973209413490302549)
      ·
        refine ⟨4591220249686047814339483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 391784127973209413490302549 4591220249686047814339483)
        ·
          refine ⟨6886830374529071721509225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4591220249686047814339483 6886830374529071721509225)
          ·
            refine ⟨5165122780896803791131919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6886830374529071721509225 5165122780896803791131919)
            ·
              refine ⟨7747684171345205686697879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5165122780896803791131919 7747684171345205686697879)
              ·
                refine ⟨11621526257017808530046819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7747684171345205686697879 11621526257017808530046819)
                ·
                  refine ⟨17432289385526712795070229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11621526257017808530046819 17432289385526712795070229)
                  ·
                    refine ⟨817138564946564662268917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17432289385526712795070229 817138564946564662268917)
                    ·
                      rfl

theorem cell23_4774115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 6].length) (baseStart_4774115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774115 prefixEnd_4774115 := by exact prefixLift 4774115
  have htrace : WordTrace (prefixWord ++ tailWord_4774115) baseStart_4774115 baseEnd_4774115 := by
    simpa [prefixWord, tailWord_4774115, baseEnd_4774115] using wordTrace_append hprefix tailTrace_4774115
  have hstable : (prefixWord ++ tailWord_4774115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774115).length < 2 ^ (prefixWord ++ tailWord_4774115).sum := by decide
  have hdescent : baseEnd_4774115 < baseStart_4774115 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774138 : List Nat := [3, 1, 1, 1, 1, 5, 1, 2, 4, 1, 3]
def baseStart_4774138 : Nat := 118140960795 + 4774138 * 2 ^ 59
def prefixEnd_4774138 : Nat := 4983230072969 + 3 ^ 40 * 4774138 * 2
def baseEnd_4774138 : Nat := 2451427504894747396819145

theorem tailTrace_4774138 : CollatzResearch.WordTrace tailWord_4774138 prefixEnd_4774138 2451427504894747396819145 := by
  unfold tailWord_4774138
  simp only [CollatzResearch.WordTrace]
  refine ⟨43531779494530214675388767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116084745318747239134370045 43531779494530214675388767)
  ·
    refine ⟨65297669241795322013083151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43531779494530214675388767 65297669241795322013083151)
    ·
      refine ⟨97946503862692983019624727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65297669241795322013083151 97946503862692983019624727)
      ·
        refine ⟨146919755794039474529437091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97946503862692983019624727 146919755794039474529437091)
        ·
          refine ⟨220379633691059211794155637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146919755794039474529437091 220379633691059211794155637)
          ·
            refine ⟨20660590658536801105702091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 220379633691059211794155637 20660590658536801105702091)
            ·
              refine ⟨30990885987805201658553137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20660590658536801105702091 30990885987805201658553137)
              ·
                refine ⟨23243164490853901243914853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30990885987805201658553137 23243164490853901243914853)
                ·
                  refine ⟨4358093342035106483234035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23243164490853901243914853 4358093342035106483234035)
                  ·
                    refine ⟨6537140013052659724851053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4358093342035106483234035 6537140013052659724851053)
                    ·
                      refine ⟨2451427504894747396819145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6537140013052659724851053 2451427504894747396819145)
                      ·
                        rfl

theorem cell23_4774138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 4, 1, 3].length) (baseStart_4774138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774138 prefixEnd_4774138 := by exact prefixLift 4774138
  have htrace : WordTrace (prefixWord ++ tailWord_4774138) baseStart_4774138 baseEnd_4774138 := by
    simpa [prefixWord, tailWord_4774138, baseEnd_4774138] using wordTrace_append hprefix tailTrace_4774138
  have hstable : (prefixWord ++ tailWord_4774138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774138).length < 2 ^ (prefixWord ++ tailWord_4774138).sum := by decide
  have hdescent : baseEnd_4774138 < baseStart_4774138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774228 : List Nat := [2, 4, 1, 1, 2, 2, 1, 1, 1, 5, 3]
def baseStart_4774228 : Nat := 118140960795 + 4774228 * 2 ^ 59
def prefixEnd_4774228 : Nat := 4983230072969 + 3 ^ 40 * 4774228 * 2
def baseEnd_4774228 : Nat := 2451473718153652044693731

theorem tailTrace_4774228 : CollatzResearch.WordTrace tailWord_4774228 prefixEnd_4774228 2451473718153652044693731 := by
  unfold tailWord_4774228
  simp only [CollatzResearch.WordTrace]
  refine ⟨87065200273897402036165669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116086933698529869381554225 87065200273897402036165669)
  ·
    refine ⟨16324725051355762881781063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87065200273897402036165669 16324725051355762881781063)
    ·
      refine ⟨24487087577033644322671595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16324725051355762881781063 24487087577033644322671595)
      ·
        refine ⟨36730631365550466484007393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24487087577033644322671595 36730631365550466484007393)
        ·
          refine ⟨27547973524162849863005545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36730631365550466484007393 27547973524162849863005545)
          ·
            refine ⟨20660980143122137397254159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27547973524162849863005545 20660980143122137397254159)
            ·
              refine ⟨30991470214683206095881239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20660980143122137397254159 30991470214683206095881239)
              ·
                refine ⟨46487205322024809143821859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30991470214683206095881239 46487205322024809143821859)
                ·
                  refine ⟨69730807983037213715732789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46487205322024809143821859 69730807983037213715732789)
                  ·
                    refine ⟨6537263248409738785849949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 69730807983037213715732789 6537263248409738785849949)
                    ·
                      refine ⟨2451473718153652044693731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6537263248409738785849949 2451473718153652044693731)
                      ·
                        rfl

theorem cell23_4774228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_4774228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774228 prefixEnd_4774228 := by exact prefixLift 4774228
  have htrace : WordTrace (prefixWord ++ tailWord_4774228) baseStart_4774228 baseEnd_4774228 := by
    simpa [prefixWord, tailWord_4774228, baseEnd_4774228] using wordTrace_append hprefix tailTrace_4774228
  have hstable : (prefixWord ++ tailWord_4774228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774228).length < 2 ^ (prefixWord ++ tailWord_4774228).sum := by decide
  have hdescent : baseEnd_4774228 < baseStart_4774228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774231 : List Nat := [1, 1, 3, 2, 3, 1, 2, 2, 1, 7]
def baseStart_4774231 : Nat := 118140960795 + 4774231 * 2 ^ 59
def prefixEnd_4774231 : Nat := 4983230072969 + 3 ^ 40 * 4774231 * 2
def baseEnd_4774231 : Nat := 817158419531871844318739

theorem tailTrace_4774231 : CollatzResearch.WordTrace tailWord_4774231 prefixEnd_4774231 817158419531871844318739 := by
  unfold tailWord_4774231
  simp only [CollatzResearch.WordTrace]
  refine ⟨174130509966783935584690547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116087006644522623723127031 174130509966783935584690547)
  ·
    refine ⟨261195764950175903377035821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174130509966783935584690547 261195764950175903377035821)
    ·
      refine ⟨97948411856315963766388433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 261195764950175903377035821 97948411856315963766388433)
      ·
        refine ⟨73461308892236972824791325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97948411856315963766388433 73461308892236972824791325)
        ·
          refine ⟨27547990834588864809296747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73461308892236972824791325 27547990834588864809296747)
          ·
            refine ⟨41321986251883297213945121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27547990834588864809296747 41321986251883297213945121)
            ·
              refine ⟨30991489688912472910458841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41321986251883297213945121 30991489688912472910458841)
              ·
                refine ⟨23243617266684354682844131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30991489688912472910458841 23243617266684354682844131)
                ·
                  refine ⟨34865425900026532024266197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23243617266684354682844131 34865425900026532024266197)
                  ·
                    refine ⟨817158419531871844318739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34865425900026532024266197 817158419531871844318739)
                    ·
                      rfl

theorem cell23_4774231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 7].length) (baseStart_4774231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774231 prefixEnd_4774231 := by exact prefixLift 4774231
  have htrace : WordTrace (prefixWord ++ tailWord_4774231) baseStart_4774231 baseEnd_4774231 := by
    simpa [prefixWord, tailWord_4774231, baseEnd_4774231] using wordTrace_append hprefix tailTrace_4774231
  have hstable : (prefixWord ++ tailWord_4774231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774231).length < 2 ^ (prefixWord ++ tailWord_4774231).sum := by decide
  have hdescent : baseEnd_4774231 < baseStart_4774231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774248 : List Nat := [2, 1, 4, 2, 2, 2, 1, 1, 1, 7]
def baseStart_4774248 : Nat := 118140960795 + 4774248 * 2 ^ 59
def prefixEnd_4774248 : Nat := 4983230072969 + 3 ^ 40 * 4774248 * 2
def baseEnd_4774248 : Nat := 817161329255580655481213

theorem tailTrace_4774248 : CollatzResearch.WordTrace tailWord_4774248 prefixEnd_4774248 817161329255580655481213 := by
  unfold tailWord_4774248
  simp only [CollatzResearch.WordTrace]
  refine ⟨87065565003861173744029699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116087420005148231658706265 87065565003861173744029699)
  ·
    refine ⟨130598347505791760616044549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87065565003861173744029699 130598347505791760616044549)
    ·
      refine ⟨24487190157335955115508353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130598347505791760616044549 24487190157335955115508353)
      ·
        refine ⟨18365392618001966336631265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24487190157335955115508353 18365392618001966336631265)
        ·
          refine ⟨13774044463501474752473449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18365392618001966336631265 13774044463501474752473449)
          ·
            refine ⟨10330533347626106064355087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13774044463501474752473449 10330533347626106064355087)
            ·
              refine ⟨15495800021439159096532631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10330533347626106064355087 15495800021439159096532631)
              ·
                refine ⟨23243700032158738644798947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15495800021439159096532631 23243700032158738644798947)
                ·
                  refine ⟨34865550048238107967198421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23243700032158738644798947 34865550048238107967198421)
                  ·
                    refine ⟨817161329255580655481213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34865550048238107967198421 817161329255580655481213)
                    ·
                      rfl

theorem cell23_4774248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_4774248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774248 prefixEnd_4774248 := by exact prefixLift 4774248
  have htrace : WordTrace (prefixWord ++ tailWord_4774248) baseStart_4774248 baseEnd_4774248 := by
    simpa [prefixWord, tailWord_4774248, baseEnd_4774248] using wordTrace_append hprefix tailTrace_4774248
  have hstable : (prefixWord ++ tailWord_4774248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774248).length < 2 ^ (prefixWord ++ tailWord_4774248).sum := by decide
  have hdescent : baseEnd_4774248 < baseStart_4774248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774251 : List Nat := [1, 1, 1, 1, 2, 2, 2, 5, 1, 3, 4]
def baseStart_4774251 : Nat := 118140960795 + 4774251 * 2 ^ 59
def prefixEnd_4774251 : Nat := 4983230072969 + 3 ^ 40 * 4774251 * 2
def baseEnd_4774251 : Nat := 2451485528208705454706125

theorem tailTrace_4774251 : CollatzResearch.WordTrace tailWord_4774251 prefixEnd_4774251 2451485528208705454706125 := by
  unfold tailWord_4774251
  simp only [CollatzResearch.WordTrace]
  refine ⟨174131239426711479000418607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116087492951140986000279071 174131239426711479000418607)
  ·
    refine ⟨261196859140067218500627911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174131239426711479000418607 261196859140067218500627911)
    ·
      refine ⟨391795288710100827750941867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261196859140067218500627911 391795288710100827750941867)
      ·
        refine ⟨587692933065151241626412801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 391795288710100827750941867 587692933065151241626412801)
        ·
          refine ⟨440769699798863431219809601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 587692933065151241626412801 440769699798863431219809601)
          ·
            refine ⟨330577274849147573414857201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 440769699798863431219809601 330577274849147573414857201)
            ·
              refine ⟨247932956136860680061142901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 330577274849147573414857201 247932956136860680061142901)
              ·
                refine ⟨23243714637830688755732147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 247932956136860680061142901 23243714637830688755732147)
                ·
                  refine ⟨34865571956746033133598221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23243714637830688755732147 34865571956746033133598221)
                  ·
                    refine ⟨13074589483779762425099333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34865571956746033133598221 13074589483779762425099333)
                    ·
                      refine ⟨2451485528208705454706125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13074589483779762425099333 2451485528208705454706125)
                      ·
                        rfl

theorem cell23_4774251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 3, 4].length) (baseStart_4774251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774251 prefixEnd_4774251 := by exact prefixLift 4774251
  have htrace : WordTrace (prefixWord ++ tailWord_4774251) baseStart_4774251 baseEnd_4774251 := by
    simpa [prefixWord, tailWord_4774251, baseEnd_4774251] using wordTrace_append hprefix tailTrace_4774251
  have hstable : (prefixWord ++ tailWord_4774251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774251).length < 2 ^ (prefixWord ++ tailWord_4774251).sum := by decide
  have hdescent : baseEnd_4774251 < baseStart_4774251 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774329 : List Nat := [1, 2, 1, 4, 3, 2, 3, 2, 1, 4]
def baseStart_4774329 : Nat := 118140960795 + 4774329 * 2 ^ 59
def prefixEnd_4774329 : Nat := 4983230072969 + 3 ^ 40 * 4774329 * 2
def baseEnd_4774329 : Nat := 817175193233252049843589

theorem tailTrace_4774329 : CollatzResearch.WordTrace tailWord_4774329 prefixEnd_4774329 817175193233252049843589 := by
  unfold tailWord_4774329
  simp only [CollatzResearch.WordTrace]
  refine ⟨174134084320428898321758041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116089389546952598881172027 174134084320428898321758041)
  ·
    refine ⟨130600563240321673741318531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174134084320428898321758041 130600563240321673741318531)
    ·
      refine ⟨195900844860482510611977797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130600563240321673741318531 195900844860482510611977797)
      ·
        refine ⟨36731408411340470739745837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 195900844860482510611977797 36731408411340470739745837)
        ·
          refine ⟨13774278154252676527404689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36731408411340470739745837 13774278154252676527404689)
          ·
            refine ⟨10330708615689507395553517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13774278154252676527404689 10330708615689507395553517)
            ·
              refine ⟨3874015730883565273332569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10330708615689507395553517 3874015730883565273332569)
              ·
                refine ⟨2905511798162673954999427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3874015730883565273332569 2905511798162673954999427)
                ·
                  refine ⟨4358267697244010932499141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2905511798162673954999427 4358267697244010932499141)
                  ·
                    refine ⟨817175193233252049843589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4358267697244010932499141 817175193233252049843589)
                    ·
                      rfl

theorem cell23_4774329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 2, 1, 4].length) (baseStart_4774329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774329 prefixEnd_4774329 := by exact prefixLift 4774329
  have htrace : WordTrace (prefixWord ++ tailWord_4774329) baseStart_4774329 baseEnd_4774329 := by
    simpa [prefixWord, tailWord_4774329, baseEnd_4774329] using wordTrace_append hprefix tailTrace_4774329
  have hstable : (prefixWord ++ tailWord_4774329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774329).length < 2 ^ (prefixWord ++ tailWord_4774329).sum := by decide
  have hdescent : baseEnd_4774329 < baseStart_4774329 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774331 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 5]
def baseStart_4774331 : Nat := 118140960795 + 4774331 * 2 ^ 59
def prefixEnd_4774331 : Nat := 4983230072969 + 3 ^ 40 * 4774331 * 2
def baseEnd_4774331 : Nat := 2451526606661065141705757

theorem tailTrace_4774331 : CollatzResearch.WordTrace tailWord_4774331 prefixEnd_4774331 2451526606661065141705757 := by
  unfold tailWord_4774331
  simp only [CollatzResearch.WordTrace]
  refine ⟨174134157266421652663330847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116089438177614435108887231 174134157266421652663330847)
  ·
    refine ⟨261201235899632478994996271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174134157266421652663330847 261201235899632478994996271)
    ·
      refine ⟨391801853849448718492494407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261201235899632478994996271 391801853849448718492494407)
      ·
        refine ⟨587702780774173077738741611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 391801853849448718492494407 587702780774173077738741611)
        ·
          refine ⟨881554171161259616608112417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 587702780774173077738741611 881554171161259616608112417)
          ·
            refine ⟨661165628370944712456084313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 881554171161259616608112417 661165628370944712456084313)
            ·
              refine ⟨495874221278208534342063235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 661165628370944712456084313 495874221278208534342063235)
              ·
                refine ⟨743811331917312801513094853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 495874221278208534342063235 743811331917312801513094853)
                ·
                  refine ⟨139464624734496150283705285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 743811331917312801513094853 139464624734496150283705285)
                  ·
                    refine ⟨26149617137718028178194741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 139464624734496150283705285 26149617137718028178194741)
                    ·
                      refine ⟨2451526606661065141705757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26149617137718028178194741 2451526606661065141705757)
                      ·
                        rfl

theorem cell23_4774331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 5].length) (baseStart_4774331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774331 prefixEnd_4774331 := by exact prefixLift 4774331
  have htrace : WordTrace (prefixWord ++ tailWord_4774331) baseStart_4774331 baseEnd_4774331 := by
    simpa [prefixWord, tailWord_4774331, baseEnd_4774331] using wordTrace_append hprefix tailTrace_4774331
  have hstable : (prefixWord ++ tailWord_4774331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774331).length < 2 ^ (prefixWord ++ tailWord_4774331).sum := by decide
  have hdescent : baseEnd_4774331 < baseStart_4774331 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774341 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 2, 1, 10]
def baseStart_4774341 : Nat := 118140960795 + 4774341 * 2 ^ 59
def prefixEnd_4774341 : Nat := 4983230072969 + 3 ^ 40 * 4774341 * 2
def baseEnd_4774341 : Nat := 2451531741467610102580711

theorem tailTrace_4774341 : CollatzResearch.WordTrace tailWord_4774341 prefixEnd_4774341 2451531741467610102580711 := by
  unfold tailWord_4774341
  simp only [CollatzResearch.WordTrace]
  refine ⟨174134521996385424371194877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116089681330923616247463251 174134521996385424371194877)
  ·
    refine ⟨65300445748644534139198079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174134521996385424371194877 65300445748644534139198079)
    ·
      refine ⟨97950668622966801208797119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65300445748644534139198079 97950668622966801208797119)
      ·
        refine ⟨146926002934450201813195679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97950668622966801208797119 146926002934450201813195679)
        ·
          refine ⟨220389004401675302719793519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146926002934450201813195679 220389004401675302719793519)
          ·
            refine ⟨330583506602512954079690279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220389004401675302719793519 330583506602512954079690279)
            ·
              refine ⟨495875259903769431119535419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 330583506602512954079690279 495875259903769431119535419)
              ·
                refine ⟨743812889855654146679303129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 495875259903769431119535419 743812889855654146679303129)
                ·
                  refine ⟨557859667391740610009477347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 743812889855654146679303129 557859667391740610009477347)
                  ·
                    refine ⟨836789501087610915014216021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 557859667391740610009477347 836789501087610915014216021)
                    ·
                      refine ⟨2451531741467610102580711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 836789501087610915014216021 2451531741467610102580711)
                      ·
                        rfl

theorem cell23_4774341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_4774341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774341 prefixEnd_4774341 := by exact prefixLift 4774341
  have htrace : WordTrace (prefixWord ++ tailWord_4774341) baseStart_4774341 baseEnd_4774341 := by
    simpa [prefixWord, tailWord_4774341, baseEnd_4774341] using wordTrace_append hprefix tailTrace_4774341
  have hstable : (prefixWord ++ tailWord_4774341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774341).length < 2 ^ (prefixWord ++ tailWord_4774341).sum := by decide
  have hdescent : baseEnd_4774341 < baseStart_4774341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774362 : List Nat := [3, 1, 1, 2, 3, 1, 4, 1, 2, 3, 2]
def baseStart_4774362 : Nat := 118140960795 + 4774362 * 2 ^ 59
def prefixEnd_4774362 : Nat := 4983230072969 + 3 ^ 40 * 4774362 * 2
def baseEnd_4774362 : Nat := 2451542524561354520418115

theorem tailTrace_4774362 : CollatzResearch.WordTrace tailWord_4774362 prefixEnd_4774362 2451542524561354520418115 := by
  unfold tailWord_4774362
  simp only [CollatzResearch.WordTrace]
  refine ⟨43533821982327336239427335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116090191952872896638472893 43533821982327336239427335)
  ·
    refine ⟨65300732973491004359141003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43533821982327336239427335 65300732973491004359141003)
    ·
      refine ⟨97951099460236506538711505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65300732973491004359141003 97951099460236506538711505)
      ·
        refine ⟨73463324595177379904033629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97951099460236506538711505 73463324595177379904033629)
        ·
          refine ⟨27548746723191517464012611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73463324595177379904033629 27548746723191517464012611)
          ·
            refine ⟨41323120084787276196018917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27548746723191517464012611 41323120084787276196018917)
            ·
              refine ⟨7748085015897614286753547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41323120084787276196018917 7748085015897614286753547)
              ·
                refine ⟨11622127523846421430130321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7748085015897614286753547 11622127523846421430130321)
                ·
                  refine ⟨8716595642884816072597741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11622127523846421430130321 8716595642884816072597741)
                  ·
                    refine ⟨3268723366081806027224153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8716595642884816072597741 3268723366081806027224153)
                    ·
                      refine ⟨2451542524561354520418115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3268723366081806027224153 2451542524561354520418115)
                      ·
                        rfl

theorem cell23_4774362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 2, 3, 2].length) (baseStart_4774362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774362 prefixEnd_4774362 := by exact prefixLift 4774362
  have htrace : WordTrace (prefixWord ++ tailWord_4774362) baseStart_4774362 baseEnd_4774362 := by
    simpa [prefixWord, tailWord_4774362, baseEnd_4774362] using wordTrace_append hprefix tailTrace_4774362
  have hstable : (prefixWord ++ tailWord_4774362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774362).length < 2 ^ (prefixWord ++ tailWord_4774362).sum := by decide
  have hdescent : baseEnd_4774362 < baseStart_4774362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774368 : List Nat := [2, 1, 1, 3, 1, 1, 5, 2, 1, 6]
def baseStart_4774368 : Nat := 118140960795 + 4774368 * 2 ^ 59
def prefixEnd_4774368 : Nat := 4983230072969 + 3 ^ 40 * 4774368 * 2
def baseEnd_4774368 : Nat := 817181868481760498981029

theorem tailTrace_4774368 : CollatzResearch.WordTrace tailWord_4774368 prefixEnd_4774368 817181868481760498981029 := by
  unfold tailWord_4774368
  simp only [CollatzResearch.WordTrace]
  refine ⟨87067753383643803991213879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116090337844858405321618505 87067753383643803991213879)
  ·
    refine ⟨130601630075465705986820819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87067753383643803991213879 130601630075465705986820819)
    ·
      refine ⟨195902445113198558980231229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130601630075465705986820819 195902445113198558980231229)
      ·
        refine ⟨73463416917449459617586711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195902445113198558980231229 73463416917449459617586711)
        ·
          refine ⟨110195125376174189426380067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73463416917449459617586711 110195125376174189426380067)
          ·
            refine ⟨165292688064261284139570101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110195125376174189426380067 165292688064261284139570101)
            ·
              refine ⟨15496189506024495388084697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 165292688064261284139570101 15496189506024495388084697)
              ·
                refine ⟨11622142129518371541063523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15496189506024495388084697 11622142129518371541063523)
                ·
                  refine ⟨17433213194277557311595285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11622142129518371541063523 17433213194277557311595285)
                  ·
                    refine ⟨817181868481760498981029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17433213194277557311595285 817181868481760498981029)
                    ·
                      rfl

theorem cell23_4774368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 1, 6].length) (baseStart_4774368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774368 prefixEnd_4774368 := by exact prefixLift 4774368
  have htrace : WordTrace (prefixWord ++ tailWord_4774368) baseStart_4774368 baseEnd_4774368 := by
    simpa [prefixWord, tailWord_4774368, baseEnd_4774368] using wordTrace_append hprefix tailTrace_4774368
  have hstable : (prefixWord ++ tailWord_4774368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774368).length < 2 ^ (prefixWord ++ tailWord_4774368).sum := by decide
  have hdescent : baseEnd_4774368 < baseStart_4774368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774386 : List Nat := [3, 2, 1, 4, 2, 1, 1, 4, 1, 1, 3]
def baseStart_4774386 : Nat := 118140960795 + 4774386 * 2 ^ 59
def prefixEnd_4774386 : Nat := 4983230072969 + 3 ^ 40 * 4774386 * 2
def baseEnd_4774386 : Nat := 2451554848097062426518005

theorem tailTrace_4774386 : CollatzResearch.WordTrace tailWord_4774386 prefixEnd_4774386 2451554848097062426518005 := by
  unfold tailWord_4774386
  simp only [CollatzResearch.WordTrace]
  refine ⟨43534040820305599264145753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116090775520814931371055341 43534040820305599264145753)
  ·
    refine ⟨32650530615229199448109315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43534040820305599264145753 32650530615229199448109315)
    ·
      refine ⟨48975795922843799172163973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32650530615229199448109315 48975795922843799172163973)
      ·
        refine ⟨9182961735533212344780745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48975795922843799172163973 9182961735533212344780745)
        ·
          refine ⟨6887221301649909258585559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9182961735533212344780745 6887221301649909258585559)
          ·
            refine ⟨10330831952474863887878339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6887221301649909258585559 10330831952474863887878339)
            ·
              refine ⟨15496247928712295831817509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10330831952474863887878339 15496247928712295831817509)
              ·
                refine ⟨2905546486633555468465783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15496247928712295831817509 2905546486633555468465783)
                ·
                  refine ⟨4358319729950333202698675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2905546486633555468465783 4358319729950333202698675)
                  ·
                    refine ⟨6537479594925499804048013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4358319729950333202698675 6537479594925499804048013)
                    ·
                      refine ⟨2451554848097062426518005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6537479594925499804048013 2451554848097062426518005)
                      ·
                        rfl

theorem cell23_4774386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_4774386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774386 prefixEnd_4774386 := by exact prefixLift 4774386
  have htrace : WordTrace (prefixWord ++ tailWord_4774386) baseStart_4774386 baseEnd_4774386 := by
    simpa [prefixWord, tailWord_4774386, baseEnd_4774386] using wordTrace_append hprefix tailTrace_4774386
  have hstable : (prefixWord ++ tailWord_4774386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774386).length < 2 ^ (prefixWord ++ tailWord_4774386).sum := by decide
  have hdescent : baseEnd_4774386 < baseStart_4774386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774392 : List Nat := [2, 1, 2, 1, 1, 4, 2, 3, 3, 2, 2]
def baseStart_4774392 : Nat := 118140960795 + 4774392 * 2 ^ 59
def prefixEnd_4774392 : Nat := 4983230072969 + 3 ^ 40 * 4774392 * 2
def baseEnd_4774392 : Nat := 2451557928980989403042977

theorem tailTrace_4774392 : CollatzResearch.WordTrace tailWord_4774392 prefixEnd_4774392 2451557928980989403042977 := by
  unfold tailWord_4774392
  simp only [CollatzResearch.WordTrace]
  refine ⟨87068191059600330040650715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116090921412800440054200953 87068191059600330040650715)
  ·
    refine ⟨130602286589400495060976073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87068191059600330040650715 130602286589400495060976073)
    ·
      refine ⟨97951714942050371295732055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130602286589400495060976073 97951714942050371295732055)
      ·
        refine ⟨146927572413075556943598083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97951714942050371295732055 146927572413075556943598083)
        ·
          refine ⟨220391358619613335415397125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146927572413075556943598083 220391358619613335415397125)
          ·
            refine ⟨41323379741177500390386961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 220391358619613335415397125 41323379741177500390386961)
            ·
              refine ⟨30992534805883125292790221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41323379741177500390386961 30992534805883125292790221)
              ·
                refine ⟨11622200552206171984796333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30992534805883125292790221 11622200552206171984796333)
                ·
                  refine ⟨4358325207077314494298625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11622200552206171984796333 4358325207077314494298625)
                  ·
                    refine ⟨3268743905307985870723969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4358325207077314494298625 3268743905307985870723969)
                    ·
                      refine ⟨2451557928980989403042977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3268743905307985870723969 2451557928980989403042977)
                      ·
                        rfl

theorem cell23_4774392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 3, 2, 2].length) (baseStart_4774392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774392 prefixEnd_4774392 := by exact prefixLift 4774392
  have htrace : WordTrace (prefixWord ++ tailWord_4774392) baseStart_4774392 baseEnd_4774392 := by
    simpa [prefixWord, tailWord_4774392, baseEnd_4774392] using wordTrace_append hprefix tailTrace_4774392
  have hstable : (prefixWord ++ tailWord_4774392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774392).length < 2 ^ (prefixWord ++ tailWord_4774392).sum := by decide
  have hdescent : baseEnd_4774392 < baseStart_4774392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774413 : List Nat := [1, 7, 1, 1, 1, 3, 1, 1, 2, 3, 2]
def baseStart_4774413 : Nat := 118140960795 + 4774413 * 2 ^ 59
def prefixEnd_4774413 : Nat := 4983230072969 + 3 ^ 40 * 4774413 * 2
def baseEnd_4774413 : Nat := 2451568712074733820880381

theorem tailTrace_4774413 : CollatzResearch.WordTrace tailWord_4774413 prefixEnd_4774413 2451568712074733820880381 := by
  unfold tailWord_4774413
  simp only [CollatzResearch.WordTrace]
  refine ⟨174137148052124580667815893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116091432034749720445210595 174137148052124580667815893)
  ·
    refine ⟨4081339407471669859401935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 174137148052124580667815893 4081339407471669859401935)
    ·
      refine ⟨6122009111207504789102903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4081339407471669859401935 6122009111207504789102903)
      ·
        refine ⟨9183013666811257183654355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6122009111207504789102903 9183013666811257183654355)
        ·
          refine ⟨13774520500216885775481533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9183013666811257183654355 13774520500216885775481533)
          ·
            refine ⟨5165445187581332165805575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13774520500216885775481533 5165445187581332165805575)
            ·
              refine ⟨7748167781371998248708363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5165445187581332165805575 7748167781371998248708363)
              ·
                refine ⟨11622251672057997373062545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7748167781371998248708363 11622251672057997373062545)
                ·
                  refine ⟨8716688754043498029796909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11622251672057997373062545 8716688754043498029796909)
                  ·
                    refine ⟨3268758282766311761173841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8716688754043498029796909 3268758282766311761173841)
                    ·
                      refine ⟨2451568712074733820880381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3268758282766311761173841 2451568712074733820880381)
                      ·
                        rfl

theorem cell23_4774413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_4774413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774413 prefixEnd_4774413 := by exact prefixLift 4774413
  have htrace : WordTrace (prefixWord ++ tailWord_4774413) baseStart_4774413 baseEnd_4774413 := by
    simpa [prefixWord, tailWord_4774413, baseEnd_4774413] using wordTrace_append hprefix tailTrace_4774413
  have hstable : (prefixWord ++ tailWord_4774413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774413).length < 2 ^ (prefixWord ++ tailWord_4774413).sum := by decide
  have hdescent : baseEnd_4774413 < baseStart_4774413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774425 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 6, 1, 3]
def baseStart_4774425 : Nat := 118140960795 + 4774425 * 2 ^ 59
def prefixEnd_4774425 : Nat := 4983230072969 + 3 ^ 40 * 4774425 * 2
def baseEnd_4774425 : Nat := 2451574873842587773930325

theorem tailTrace_4774425 : CollatzResearch.WordTrace tailWord_4774425 prefixEnd_4774425 2451574873842587773930325 := by
  unfold tailWord_4774425
  simp only [CollatzResearch.WordTrace]
  refine ⟨174137585728081106717252729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116091723818720737811501819 174137585728081106717252729)
  ·
    refine ⟨130603189296060830037939547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174137585728081106717252729 130603189296060830037939547)
    ·
      refine ⟨195904783944091245056909321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130603189296060830037939547 195904783944091245056909321)
      ·
        refine ⟨146928587958068433792681991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195904783944091245056909321 146928587958068433792681991)
        ·
          refine ⟨220392881937102650689022987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146928587958068433792681991 220392881937102650689022987)
          ·
            refine ⟨330589322905653976033534481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220392881937102650689022987 330589322905653976033534481)
            ·
              refine ⟨247941992179240482025150861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 330589322905653976033534481 247941992179240482025150861)
              ·
                refine ⟨92978247067215180759431573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 247941992179240482025150861 92978247067215180759431573)
                ·
                  refine ⟨4358355331275711598098355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 92978247067215180759431573 4358355331275711598098355)
                  ·
                    refine ⟨6537532996913567397147533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4358355331275711598098355 6537532996913567397147533)
                    ·
                      refine ⟨2451574873842587773930325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6537532996913567397147533 2451574873842587773930325)
                      ·
                        rfl

theorem cell23_4774425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 6, 1, 3].length) (baseStart_4774425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774425 prefixEnd_4774425 := by exact prefixLift 4774425
  have htrace : WordTrace (prefixWord ++ tailWord_4774425) baseStart_4774425 baseEnd_4774425 := by
    simpa [prefixWord, tailWord_4774425, baseEnd_4774425] using wordTrace_append hprefix tailTrace_4774425
  have hstable : (prefixWord ++ tailWord_4774425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774425).length < 2 ^ (prefixWord ++ tailWord_4774425).sum := by decide
  have hdescent : baseEnd_4774425 < baseStart_4774425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774429 : List Nat := [1, 4, 2, 2, 1, 2, 4, 1, 1, 2, 3]
def baseStart_4774429 : Nat := 118140960795 + 4774429 * 2 ^ 59
def prefixEnd_4774429 : Nat := 4983230072969 + 3 ^ 40 * 4774429 * 2
def baseEnd_4774429 : Nat := 2451576927765205758280307

theorem tailTrace_4774429 : CollatzResearch.WordTrace tailWord_4774429 prefixEnd_4774429 2451576927765205758280307 := by
  unfold tailWord_4774429
  simp only [CollatzResearch.WordTrace]
  refine ⟨174137731620066615400398341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116091821080044410266932227 174137731620066615400398341)
  ·
    refine ⟨32650824678762490387574689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174137731620066615400398341 32650824678762490387574689)
    ·
      refine ⟨24488118509071867790681017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32650824678762490387574689 24488118509071867790681017)
      ·
        refine ⟨18366088881803900843010763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24488118509071867790681017 18366088881803900843010763)
        ·
          refine ⟨27549133322705851264516145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18366088881803900843010763 27549133322705851264516145)
          ·
            refine ⟨20661849992029388448387109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27549133322705851264516145 20661849992029388448387109)
            ·
              refine ⟨3874096873505510334072583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20661849992029388448387109 3874096873505510334072583)
              ·
                refine ⟨5811145310258265501108875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3874096873505510334072583 5811145310258265501108875)
                ·
                  refine ⟨8716717965387398251663313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5811145310258265501108875 8716717965387398251663313)
                  ·
                    refine ⟨6537538474040548688747485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8716717965387398251663313 6537538474040548688747485)
                    ·
                      refine ⟨2451576927765205758280307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6537538474040548688747485 2451576927765205758280307)
                      ·
                        rfl

theorem cell23_4774429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_4774429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774429 prefixEnd_4774429 := by exact prefixLift 4774429
  have htrace : WordTrace (prefixWord ++ tailWord_4774429) baseStart_4774429 baseEnd_4774429 := by
    simpa [prefixWord, tailWord_4774429, baseEnd_4774429] using wordTrace_append hprefix tailTrace_4774429
  have hstable : (prefixWord ++ tailWord_4774429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774429).length < 2 ^ (prefixWord ++ tailWord_4774429).sum := by decide
  have hdescent : baseEnd_4774429 < baseStart_4774429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774436 : List Nat := [2, 3, 1, 5, 1, 2, 1, 2, 2, 4]
def baseStart_4774436 : Nat := 118140960795 + 4774436 * 2 ^ 59
def prefixEnd_4774436 : Nat := 4983230072969 + 3 ^ 40 * 4774436 * 2
def baseEnd_4774436 : Nat := 817193507376595743630925

theorem tailTrace_4774436 : CollatzResearch.WordTrace tailWord_4774436 prefixEnd_4774436 817193507376595743630925 := by
  unfold tailWord_4774436
  simp only [CollatzResearch.WordTrace]
  refine ⟨87068993465520627797951581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116091991287360837063935441 87068993465520627797951581)
  ·
    refine ⟨32650872549570235424231843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87068993465520627797951581 32650872549570235424231843)
    ·
      refine ⟨48976308824355353136347765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32650872549570235424231843 48976308824355353136347765)
      ·
        refine ⟨4591528952283314356532603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48976308824355353136347765 4591528952283314356532603)
        ·
          refine ⟨6887293428424971534798905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4591528952283314356532603 6887293428424971534798905)
          ·
            refine ⟨5165470071318728651099179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6887293428424971534798905 5165470071318728651099179)
            ·
              refine ⟨7748205106978092976648769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5165470071318728651099179 7748205106978092976648769)
              ·
                refine ⟨5811153830233569732486577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7748205106978092976648769 5811153830233569732486577)
                ·
                  refine ⟨4358365372675177299364933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5811153830233569732486577 4358365372675177299364933)
                  ·
                    refine ⟨817193507376595743630925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4358365372675177299364933 817193507376595743630925)
                    ·
                      rfl

theorem cell23_4774436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 2, 2, 4].length) (baseStart_4774436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774436 prefixEnd_4774436 := by exact prefixLift 4774436
  have htrace : WordTrace (prefixWord ++ tailWord_4774436) baseStart_4774436 baseEnd_4774436 := by
    simpa [prefixWord, tailWord_4774436, baseEnd_4774436] using wordTrace_append hprefix tailTrace_4774436
  have hstable : (prefixWord ++ tailWord_4774436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774436).length < 2 ^ (prefixWord ++ tailWord_4774436).sum := by decide
  have hdescent : baseEnd_4774436 < baseStart_4774436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774448 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 4]
def baseStart_4774448 : Nat := 118140960795 + 4774448 * 2 ^ 59
def prefixEnd_4774448 : Nat := 4983230072969 + 3 ^ 40 * 4774448 * 2
def baseEnd_4774448 : Nat := 2451586683897641183942719

theorem tailTrace_4774448 : CollatzResearch.WordTrace tailWord_4774448 prefixEnd_4774448 2451586683897641183942719 := by
  unfold tailWord_4774448
  simp only [CollatzResearch.WordTrace]
  refine ⟨87069212303498890822669999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116092283071331854430226665 87069212303498890822669999)
  ·
    refine ⟨130603818455248336234004999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87069212303498890822669999 130603818455248336234004999)
    ·
      refine ⟨195905727682872504351007499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130603818455248336234004999 195905727682872504351007499)
      ·
        refine ⟨293858591524308756526511249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195905727682872504351007499 293858591524308756526511249)
        ·
          refine ⟨220393943643231567394883437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 293858591524308756526511249 220393943643231567394883437)
          ·
            refine ⟨82647728866211837773081289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 220393943643231567394883437 82647728866211837773081289)
            ·
              refine ⟨61985796649658878329810967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82647728866211837773081289 61985796649658878329810967)
              ·
                refine ⟨92978694974488317494716451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61985796649658878329810967 92978694974488317494716451)
                ·
                  refine ⟨139468042461732476242074677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92978694974488317494716451 139468042461732476242074677)
                  ·
                    refine ⟨13075128980787419647694501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 139468042461732476242074677 13075128980787419647694501)
                    ·
                      refine ⟨2451586683897641183942719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13075128980787419647694501 2451586683897641183942719)
                      ·
                        rfl

theorem cell23_4774448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 4].length) (baseStart_4774448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774448 prefixEnd_4774448 := by exact prefixLift 4774448
  have htrace : WordTrace (prefixWord ++ tailWord_4774448) baseStart_4774448 baseEnd_4774448 := by
    simpa [prefixWord, tailWord_4774448, baseEnd_4774448] using wordTrace_append hprefix tailTrace_4774448
  have hstable : (prefixWord ++ tailWord_4774448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774448).length < 2 ^ (prefixWord ++ tailWord_4774448).sum := by decide
  have hdescent : baseEnd_4774448 < baseStart_4774448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774469 : List Nat := [1, 3, 1, 1, 1, 6, 2, 2, 1, 3, 2]
def baseStart_4774469 : Nat := 118140960795 + 4774469 * 2 ^ 59
def prefixEnd_4774469 : Nat := 4983230072969 + 3 ^ 40 * 4774469 * 2
def baseEnd_4774469 : Nat := 2451597466991385601780123

theorem tailTrace_4774469 : CollatzResearch.WordTrace tailWord_4774469 prefixEnd_4774469 2451597466991385601780123 := by
  unfold tailWord_4774469
  simp only [CollatzResearch.WordTrace]
  refine ⟨174139190539921702231854461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116092793693281134821236307 174139190539921702231854461)
  ·
    refine ⟨65302196452470638336945423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174139190539921702231854461 65302196452470638336945423)
    ·
      refine ⟨97953294678705957505418135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65302196452470638336945423 97953294678705957505418135)
      ·
        refine ⟨146929942018058936258127203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97953294678705957505418135 146929942018058936258127203)
        ·
          refine ⟨220394913027088404387190805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146929942018058936258127203 220394913027088404387190805)
          ·
            refine ⟨10331011548144768955649569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 220394913027088404387190805 10331011548144768955649569)
            ·
              refine ⟨7748258661108576716737177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10331011548144768955649569 7748258661108576716737177)
              ·
                refine ⟨5811193995831432537552883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7748258661108576716737177 5811193995831432537552883)
                ·
                  refine ⟨8716790993747148806329325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5811193995831432537552883 8716790993747148806329325)
                  ·
                    refine ⟨3268796622655180802373497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8716790993747148806329325 3268796622655180802373497)
                    ·
                      refine ⟨2451597466991385601780123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3268796622655180802373497 2451597466991385601780123)
                      ·
                        rfl

theorem cell23_4774469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 2, 1, 3, 2].length) (baseStart_4774469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774469 prefixEnd_4774469 := by exact prefixLift 4774469
  have htrace : WordTrace (prefixWord ++ tailWord_4774469) baseStart_4774469 baseEnd_4774469 := by
    simpa [prefixWord, tailWord_4774469, baseEnd_4774469] using wordTrace_append hprefix tailTrace_4774469
  have hstable : (prefixWord ++ tailWord_4774469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774469).length < 2 ^ (prefixWord ++ tailWord_4774469).sum := by decide
  have hdescent : baseEnd_4774469 < baseStart_4774469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774482 : List Nat := [3, 2, 2, 1, 2, 1, 2, 1, 3, 4, 2]
def baseStart_4774482 : Nat := 118140960795 + 4774482 * 2 ^ 59
def prefixEnd_4774482 : Nat := 4983230072969 + 3 ^ 40 * 4774482 * 2
def baseEnd_4774482 : Nat := 2451604142239894050917563

theorem tailTrace_4774482 : CollatzResearch.WordTrace tailWord_4774482 prefixEnd_4774482 2451604142239894050917563 := by
  unfold tailWord_4774482
  simp only [CollatzResearch.WordTrace]
  refine ⟨43534916172218651363019425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116093109792583070301385133 43534916172218651363019425)
  ·
    refine ⟨32651187129163988522264569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43534916172218651363019425 32651187129163988522264569)
    ·
      refine ⟨24488390346872991391698427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32651187129163988522264569 24488390346872991391698427)
      ·
        refine ⟨36732585520309487087547641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24488390346872991391698427 36732585520309487087547641)
        ·
          refine ⟨27549439140232115315660731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36732585520309487087547641 27549439140232115315660731)
          ·
            refine ⟨41324158710348172973491097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27549439140232115315660731 41324158710348172973491097)
            ·
              refine ⟨30993119032761129730118323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41324158710348172973491097 30993119032761129730118323)
              ·
                refine ⟨46489678549141694595177485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30993119032761129730118323 46489678549141694595177485)
                ·
                  refine ⟨17433629455928135473191557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46489678549141694595177485 17433629455928135473191557)
                  ·
                    refine ⟨3268805522986525401223417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17433629455928135473191557 3268805522986525401223417)
                    ·
                      refine ⟨2451604142239894050917563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3268805522986525401223417 2451604142239894050917563)
                      ·
                        rfl

theorem cell23_4774482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 3, 4, 2].length) (baseStart_4774482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774482 prefixEnd_4774482 := by exact prefixLift 4774482
  have htrace : WordTrace (prefixWord ++ tailWord_4774482) baseStart_4774482 baseEnd_4774482 := by
    simpa [prefixWord, tailWord_4774482, baseEnd_4774482] using wordTrace_append hprefix tailTrace_4774482
  have hstable : (prefixWord ++ tailWord_4774482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774482).length < 2 ^ (prefixWord ++ tailWord_4774482).sum := by decide
  have hdescent : baseEnd_4774482 < baseStart_4774482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774488 : List Nat := [2, 1, 2, 2, 1, 2, 2, 2, 9]
def baseStart_4774488 : Nat := 118140960795 + 4774488 * 2 ^ 59
def prefixEnd_4774488 : Nat := 4983230072969 + 3 ^ 40 * 4774488 * 2
def baseEnd_4774488 : Nat := 272400802569313447493615

theorem tailTrace_4774488 : CollatzResearch.WordTrace tailWord_4774488 prefixEnd_4774488 272400802569313447493615 := by
  unfold tailWord_4774488
  simp only [CollatzResearch.WordTrace]
  refine ⟨87069941763426434238398059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116093255684568578984530745 87069941763426434238398059)
  ·
    refine ⟨130604912645139651357597089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87069941763426434238398059 130604912645139651357597089)
    ·
      refine ⟨97953684483854738518197817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130604912645139651357597089 97953684483854738518197817)
      ·
        refine ⟨73465263362891053888648363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97953684483854738518197817 73465263362891053888648363)
        ·
          refine ⟨110197895044336580832972545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73465263362891053888648363 110197895044336580832972545)
          ·
            refine ⟨82648421283252435624729409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110197895044336580832972545 82648421283252435624729409)
            ·
              refine ⟨61986315962439326718547057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82648421283252435624729409 61986315962439326718547057)
              ·
                refine ⟨46489736971829495038910293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61986315962439326718547057 46489736971829495038910293)
                ·
                  refine ⟨272400802569313447493615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 46489736971829495038910293 272400802569313447493615)
                  ·
                    rfl

theorem cell23_4774488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 9].length) (baseStart_4774488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774488 prefixEnd_4774488 := by exact prefixLift 4774488
  have htrace : WordTrace (prefixWord ++ tailWord_4774488) baseStart_4774488 baseEnd_4774488 := by
    simpa [prefixWord, tailWord_4774488, baseEnd_4774488] using wordTrace_append hprefix tailTrace_4774488
  have hstable : (prefixWord ++ tailWord_4774488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774488).length < 2 ^ (prefixWord ++ tailWord_4774488).sum := by decide
  have hdescent : baseEnd_4774488 < baseStart_4774488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774494 : List Nat := [4, 4, 1, 2, 1, 1, 3, 2, 1, 2, 2]
def baseStart_4774494 : Nat := 118140960795 + 4774494 * 2 ^ 59
def prefixEnd_4774494 : Nat := 4983230072969 + 3 ^ 40 * 4774494 * 2
def baseEnd_4774494 : Nat := 2451610304007748003967509

theorem tailTrace_4774494 : CollatzResearch.WordTrace tailWord_4774494 prefixEnd_4774494 2451610304007748003967509 := by
  unfold tailWord_4774494
  simp only [CollatzResearch.WordTrace]
  refine ⟨21767512795603891437689317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116093401576554087667676357 21767512795603891437689317)
  ·
    refine ⟨4081408649175729644566747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21767512795603891437689317 4081408649175729644566747)
    ·
      refine ⟨6122112973763594466850121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4081408649175729644566747 6122112973763594466850121)
      ·
        refine ⟨4591584730322695850137591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6122112973763594466850121 4591584730322695850137591)
        ·
          refine ⟨6887377095484043775206387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4591584730322695850137591 6887377095484043775206387)
          ·
            refine ⟨10331065643226065662809581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6887377095484043775206387 10331065643226065662809581)
            ·
              refine ⟨3874149616209774623553593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10331065643226065662809581 3874149616209774623553593)
              ·
                refine ⟨2905612212157330967665195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3874149616209774623553593 2905612212157330967665195)
                ·
                  refine ⟨4358418318235996451497793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2905612212157330967665195 4358418318235996451497793)
                  ·
                    refine ⟨3268813738676997338623345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4358418318235996451497793 3268813738676997338623345)
                    ·
                      refine ⟨2451610304007748003967509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3268813738676997338623345 2451610304007748003967509)
                      ·
                        rfl

theorem cell23_4774494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_4774494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774494 prefixEnd_4774494 := by exact prefixLift 4774494
  have htrace : WordTrace (prefixWord ++ tailWord_4774494) baseStart_4774494 baseEnd_4774494 := by
    simpa [prefixWord, tailWord_4774494, baseEnd_4774494] using wordTrace_append hprefix tailTrace_4774494
  have hstable : (prefixWord ++ tailWord_4774494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774494).length < 2 ^ (prefixWord ++ tailWord_4774494).sum := by decide
  have hdescent : baseEnd_4774494 < baseStart_4774494 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774499 : List Nat := [1, 1, 1, 5, 1, 2, 2, 4, 2, 2, 2]
def baseStart_4774499 : Nat := 118140960795 + 4774499 * 2 ^ 59
def prefixEnd_4774499 : Nat := 4983230072969 + 3 ^ 40 * 4774499 * 2
def baseEnd_4774499 : Nat := 2451612871411020484404985

theorem tailTrace_4774499 : CollatzResearch.WordTrace tailWord_4774499 prefixEnd_4774499 2451612871411020484404985 := by
  unfold tailWord_4774499
  simp only [CollatzResearch.WordTrace]
  refine ⟨174140284729813017355446551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116093523153208678236964367 174140284729813017355446551)
  ·
    refine ⟨261210427094719526033169827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174140284729813017355446551 261210427094719526033169827)
    ·
      refine ⟨391815640642079289049754741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261210427094719526033169827 391815640642079289049754741)
      ·
        refine ⟨36732716310194933348414507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 391815640642079289049754741 36732716310194933348414507)
        ·
          refine ⟨55099074465292400022621761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36732716310194933348414507 55099074465292400022621761)
          ·
            refine ⟨41324305848969300016966321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55099074465292400022621761 41324305848969300016966321)
            ·
              refine ⟨30993229386726975012724741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41324305848969300016966321 30993229386726975012724741)
              ·
                refine ⟨5811230510011307814885889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30993229386726975012724741 5811230510011307814885889)
                ·
                  refine ⟨4358422882508480861164417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5811230510011307814885889 4358422882508480861164417)
                  ·
                    refine ⟨3268817161881360645873313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4358422882508480861164417 3268817161881360645873313)
                    ·
                      refine ⟨2451612871411020484404985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3268817161881360645873313 2451612871411020484404985)
                      ·
                        rfl

theorem cell23_4774499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4, 2, 2, 2].length) (baseStart_4774499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774499 prefixEnd_4774499 := by exact prefixLift 4774499
  have htrace : WordTrace (prefixWord ++ tailWord_4774499) baseStart_4774499 baseEnd_4774499 := by
    simpa [prefixWord, tailWord_4774499, baseEnd_4774499] using wordTrace_append hprefix tailTrace_4774499
  have hstable : (prefixWord ++ tailWord_4774499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774499).length < 2 ^ (prefixWord ++ tailWord_4774499).sum := by decide
  have hdescent : baseEnd_4774499 < baseStart_4774499 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774556 : List Nat := [2, 2, 3, 2, 2, 3, 2, 2, 5]
def baseStart_4774556 : Nat := 118140960795 + 4774556 * 2 ^ 59
def prefixEnd_4774556 : Nat := 4983230072969 + 3 ^ 40 * 4774556 * 2
def baseEnd_4774556 : Nat := 272404682200925195710247

theorem tailTrace_4774556 : CollatzResearch.WordTrace tailWord_4774556 prefixEnd_4774556 272404682200925195710247 := by
  unfold tailWord_4774556
  simp only [CollatzResearch.WordTrace]
  refine ⟨87071181845303258045135761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116094909127071010726847681 87071181845303258045135761)
  ·
    refine ⟨65303386383977443533851821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87071181845303258045135761 65303386383977443533851821)
    ·
      refine ⟨24488769893991541325194433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65303386383977443533851821 24488769893991541325194433)
      ·
        refine ⟨18366577420493655993895825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24488769893991541325194433 18366577420493655993895825)
        ·
          refine ⟨13774933065370241995421869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18366577420493655993895825 13774933065370241995421869)
          ·
            refine ⟨5165599899513840748283201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13774933065370241995421869 5165599899513840748283201)
            ·
              refine ⟨3874199924635380561212401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5165599899513840748283201 3874199924635380561212401)
              ·
                refine ⟨2905649943476535420909301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3874199924635380561212401 2905649943476535420909301)
                ·
                  refine ⟨272404682200925195710247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2905649943476535420909301 272404682200925195710247)
                  ·
                    rfl

theorem cell23_4774556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 2, 5].length) (baseStart_4774556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774556 prefixEnd_4774556 := by exact prefixLift 4774556
  have htrace : WordTrace (prefixWord ++ tailWord_4774556) baseStart_4774556 baseEnd_4774556 := by
    simpa [prefixWord, tailWord_4774556, baseEnd_4774556] using wordTrace_append hprefix tailTrace_4774556
  have hstable : (prefixWord ++ tailWord_4774556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774556).length < 2 ^ (prefixWord ++ tailWord_4774556).sum := by decide
  have hdescent : baseEnd_4774556 < baseStart_4774556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774589 : List Nat := [1, 4, 1, 2, 1, 5, 1, 1, 2, 1, 4]
def baseStart_4774589 : Nat := 118140960795 + 4774589 * 2 ^ 59
def prefixEnd_4774589 : Nat := 4983230072969 + 3 ^ 40 * 4774589 * 2
def baseEnd_4774589 : Nat := 2451659084669925132279571

theorem tailTrace_4774589 : CollatzResearch.WordTrace tailWord_4774589 prefixEnd_4774589 2451659084669925132279571 := by
  unfold tailWord_4774589
  simp only [CollatzResearch.WordTrace]
  refine ⟨174143567299486962726222821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116095711532991308484148547 174143567299486962726222821)
  ·
    refine ⟨32651918868653805511166779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174143567299486962726222821 32651918868653805511166779)
    ·
      refine ⟨48977878302980708266750169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32651918868653805511166779 48977878302980708266750169)
      ·
        refine ⟨36733408727235531200062627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48977878302980708266750169 36733408727235531200062627)
        ·
          refine ⟨55100113090853296800093941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36733408727235531200062627 55100113090853296800093941)
          ·
            refine ⟨5165635602267496575008807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55100113090853296800093941 5165635602267496575008807)
            ·
              refine ⟨7748453403401244862513211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5165635602267496575008807 7748453403401244862513211)
              ·
                refine ⟨11622680105101867293769817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7748453403401244862513211 11622680105101867293769817)
                ·
                  refine ⟨8717010078826400470327363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11622680105101867293769817 8717010078826400470327363)
                  ·
                    refine ⟨13075515118239600705491045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8717010078826400470327363 13075515118239600705491045)
                    ·
                      refine ⟨2451659084669925132279571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13075515118239600705491045 2451659084669925132279571)
                      ·
                        rfl

theorem cell23_4774589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_4774589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774589 prefixEnd_4774589 := by exact prefixLift 4774589
  have htrace : WordTrace (prefixWord ++ tailWord_4774589) baseStart_4774589 baseEnd_4774589 := by
    simpa [prefixWord, tailWord_4774589, baseEnd_4774589] using wordTrace_append hprefix tailTrace_4774589
  have hstable : (prefixWord ++ tailWord_4774589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774589).length < 2 ^ (prefixWord ++ tailWord_4774589).sum := by decide
  have hdescent : baseEnd_4774589 < baseStart_4774589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774592 : List Nat := [2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 3]
def baseStart_4774592 : Nat := 118140960795 + 4774592 * 2 ^ 59
def prefixEnd_4774592 : Nat := 4983230072969 + 3 ^ 40 * 4774592 * 2
def baseEnd_4774592 : Nat := 2451660625111888620542057

theorem tailTrace_4774592 : CollatzResearch.WordTrace tailWord_4774592 prefixEnd_4774592 2451660625111888620542057 := by
  unfold tailWord_4774592
  simp only [CollatzResearch.WordTrace]
  refine ⟨87071838359238047119291015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116095784478984062825721353 87071838359238047119291015)
  ·
    refine ⟨130607757538857070678936523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87071838359238047119291015 130607757538857070678936523)
    ·
      refine ⟨195911636308285606018404785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130607757538857070678936523 195911636308285606018404785)
      ·
        refine ⟨146933727231214204513803589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195911636308285606018404785 146933727231214204513803589)
        ·
          refine ⟨27550073855852663346338173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 146933727231214204513803589 27550073855852663346338173)
          ·
            refine ⟨10331277695944748754876815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27550073855852663346338173 10331277695944748754876815)
            ·
              refine ⟨15496916543917123132315223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10331277695944748754876815 15496916543917123132315223)
              ·
                refine ⟨23245374815875684698472835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15496916543917123132315223 23245374815875684698472835)
                ·
                  refine ⟨34868062223813527047709253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23245374815875684698472835 34868062223813527047709253)
                  ·
                    refine ⟨6537761666965036321445485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34868062223813527047709253 6537761666965036321445485)
                    ·
                      refine ⟨2451660625111888620542057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6537761666965036321445485 2451660625111888620542057)
                      ·
                        rfl

theorem cell23_4774592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 3].length) (baseStart_4774592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774592 prefixEnd_4774592 := by exact prefixLift 4774592
  have htrace : WordTrace (prefixWord ++ tailWord_4774592) baseStart_4774592 baseEnd_4774592 := by
    simpa [prefixWord, tailWord_4774592, baseEnd_4774592] using wordTrace_append hprefix tailTrace_4774592
  have hstable : (prefixWord ++ tailWord_4774592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774592).length < 2 ^ (prefixWord ++ tailWord_4774592).sum := by decide
  have hdescent : baseEnd_4774592 < baseStart_4774592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774615 : List Nat := [1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 6]
def baseStart_4774615 : Nat := 118140960795 + 4774615 * 2 ^ 59
def prefixEnd_4774615 : Nat := 4983230072969 + 3 ^ 40 * 4774615 * 2
def baseEnd_4774615 : Nat := 2451672435166942030554451

theorem tailTrace_4774615 : CollatzResearch.WordTrace tailWord_4774615 prefixEnd_4774615 2451672435166942030554451 := by
  unfold tailWord_4774615
  simp only [CollatzResearch.WordTrace]
  refine ⟨174144515597392769166669299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116096343731595179444446199 174144515597392769166669299)
  ·
    refine ⟨261216773396089153750003949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174144515597392769166669299 261216773396089153750003949)
    ·
      refine ⟨97956290023533432656251481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 261216773396089153750003949 97956290023533432656251481)
      ·
        refine ⟨73467217517650074492188611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97956290023533432656251481 73467217517650074492188611)
        ·
          refine ⟨110200826276475111738282917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73467217517650074492188611 110200826276475111738282917)
          ·
            refine ⟨20662654926839083450928047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110200826276475111738282917 20662654926839083450928047)
            ·
              refine ⟨30993982390258625176392071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20662654926839083450928047 30993982390258625176392071)
              ·
                refine ⟨46490973585387937764588107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30993982390258625176392071 46490973585387937764588107)
                ·
                  refine ⟨69736460378081906646882161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46490973585387937764588107 69736460378081906646882161)
                  ·
                    refine ⟨52302345283561429985161621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 69736460378081906646882161 52302345283561429985161621)
                    ·
                      refine ⟨2451672435166942030554451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52302345283561429985161621 2451672435166942030554451)
                      ·
                        rfl

theorem cell23_4774615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_4774615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774615 prefixEnd_4774615 := by exact prefixLift 4774615
  have htrace : WordTrace (prefixWord ++ tailWord_4774615) baseStart_4774615 baseEnd_4774615 := by
    simpa [prefixWord, tailWord_4774615, baseEnd_4774615] using wordTrace_append hprefix tailTrace_4774615
  have hstable : (prefixWord ++ tailWord_4774615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774615).length < 2 ^ (prefixWord ++ tailWord_4774615).sum := by decide
  have hdescent : baseEnd_4774615 < baseStart_4774615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774629 : List Nat := [1, 3, 1, 4, 1, 3, 3, 1, 6]
def baseStart_4774629 : Nat := 118140960795 + 4774629 * 2 ^ 59
def prefixEnd_4774629 : Nat := 4983230072969 + 3 ^ 40 * 4774629 * 2
def baseEnd_4774629 : Nat := 272408847099567219531043

theorem tailTrace_4774629 : CollatzResearch.WordTrace tailWord_4774629 prefixEnd_4774629 272408847099567219531043 := by
  unfold tailWord_4774629
  simp only [CollatzResearch.WordTrace]
  refine ⟨174145026219342049557678941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116096684146228033038452627 174145026219342049557678941)
  ·
    refine ⟨65304384832253268584129603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174145026219342049557678941 65304384832253268584129603)
    ·
      refine ⟨97956577248379902876194405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65304384832253268584129603 97956577248379902876194405)
      ·
        refine ⟨18366858234071231789286451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97956577248379902876194405 18366858234071231789286451)
        ·
          refine ⟨27550287351106847683929677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18366858234071231789286451 27550287351106847683929677)
          ·
            refine ⟨10331357756665067881473629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27550287351106847683929677 10331357756665067881473629)
            ·
              refine ⟨3874259158749400455552611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10331357756665067881473629 3874259158749400455552611)
              ·
                refine ⟨5811388738124100683328917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3874259158749400455552611 5811388738124100683328917)
                ·
                  refine ⟨272408847099567219531043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5811388738124100683328917 272408847099567219531043)
                  ·
                    rfl

theorem cell23_4774629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 1, 6].length) (baseStart_4774629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774629 prefixEnd_4774629 := by exact prefixLift 4774629
  have htrace : WordTrace (prefixWord ++ tailWord_4774629) baseStart_4774629 baseEnd_4774629 := by
    simpa [prefixWord, tailWord_4774629, baseEnd_4774629] using wordTrace_append hprefix tailTrace_4774629
  have hstable : (prefixWord ++ tailWord_4774629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774629).length < 2 ^ (prefixWord ++ tailWord_4774629).sum := by decide
  have hdescent : baseEnd_4774629 < baseStart_4774629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774639 : List Nat := [1, 1, 2, 1, 5, 2, 2, 2, 3, 1, 3]
def baseStart_4774639 : Nat := 118140960795 + 4774639 * 2 ^ 59
def prefixEnd_4774639 : Nat := 4983230072969 + 3 ^ 40 * 4774639 * 2
def baseEnd_4774639 : Nat := 2451684758702649936654341

theorem tailTrace_4774639 : CollatzResearch.WordTrace tailWord_4774639 prefixEnd_4774639 2451684758702649936654341 := by
  unfold tailWord_4774639
  simp only [CollatzResearch.WordTrace]
  refine ⟨174145390949305821265542971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116096927299537214177028647 174145390949305821265542971)
  ·
    refine ⟨261218086423958731898314457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174145390949305821265542971 261218086423958731898314457)
    ·
      refine ⟨195913564817969048923735843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261218086423958731898314457 195913564817969048923735843)
      ·
        refine ⟨293870347226953573385603765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195913564817969048923735843 293870347226953573385603765)
        ·
          refine ⟨27550345052526897504900353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 293870347226953573385603765 27550345052526897504900353)
          ·
            refine ⟨20662758789395173128675265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27550345052526897504900353 20662758789395173128675265)
            ·
              refine ⟨15497069092046379846506449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20662758789395173128675265 15497069092046379846506449)
              ·
                refine ⟨11622801819034784884879837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15497069092046379846506449 11622801819034784884879837)
                ·
                  refine ⟨4358550682138044331829939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11622801819034784884879837 4358550682138044331829939)
                  ·
                    refine ⟨6537826023207066497744909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4358550682138044331829939 6537826023207066497744909)
                    ·
                      refine ⟨2451684758702649936654341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6537826023207066497744909 2451684758702649936654341)
                      ·
                        rfl

theorem cell23_4774639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 3, 1, 3].length) (baseStart_4774639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774639 prefixEnd_4774639 := by exact prefixLift 4774639
  have htrace : WordTrace (prefixWord ++ tailWord_4774639) baseStart_4774639 baseEnd_4774639 := by
    simpa [prefixWord, tailWord_4774639, baseEnd_4774639] using wordTrace_append hprefix tailTrace_4774639
  have hstable : (prefixWord ++ tailWord_4774639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774639).length < 2 ^ (prefixWord ++ tailWord_4774639).sum := by decide
  have hdescent : baseEnd_4774639 < baseStart_4774639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774655 : List Nat := [1, 1, 2, 2, 1, 3, 1, 3, 3, 6]
def baseStart_4774655 : Nat := 118140960795 + 4774655 * 2 ^ 59
def prefixEnd_4774655 : Nat := 4983230072969 + 3 ^ 40 * 4774655 * 2
def baseEnd_4774655 : Nat := 817230991464373958018089

theorem tailTrace_4774655 : CollatzResearch.WordTrace tailWord_4774655 prefixEnd_4774655 817230991464373958018089 := by
  unfold tailWord_4774655
  simp only [CollatzResearch.WordTrace]
  refine ⟨174145974517247855998125419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116097316344831903998750279 174145974517247855998125419)
  ·
    refine ⟨261218961775871783997188129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174145974517247855998125419 261218961775871783997188129)
    ·
      refine ⟨195914221331903837997891097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261218961775871783997188129 195914221331903837997891097)
      ·
        refine ⟨146935665998927878498418323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195914221331903837997891097 146935665998927878498418323)
        ·
          refine ⟨220403498998391817747627485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146935665998927878498418323 220403498998391817747627485)
          ·
            refine ⟨82651312124396931655360307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 220403498998391817747627485 82651312124396931655360307)
            ·
              refine ⟨123976968186595397483040461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82651312124396931655360307 123976968186595397483040461)
              ·
                refine ⟨46491363069973274056140173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123976968186595397483040461 46491363069973274056140173)
                ·
                  refine ⟨17434261151239977771052565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46491363069973274056140173 17434261151239977771052565)
                  ·
                    refine ⟨817230991464373958018089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17434261151239977771052565 817230991464373958018089)
                    ·
                      rfl

theorem cell23_4774655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 6].length) (baseStart_4774655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774655 prefixEnd_4774655 := by exact prefixLift 4774655
  have htrace : WordTrace (prefixWord ++ tailWord_4774655) baseStart_4774655 baseEnd_4774655 := by
    simpa [prefixWord, tailWord_4774655, baseEnd_4774655] using wordTrace_append hprefix tailTrace_4774655
  have hstable : (prefixWord ++ tailWord_4774655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774655).length < 2 ^ (prefixWord ++ tailWord_4774655).sum := by decide
  have hdescent : baseEnd_4774655 < baseStart_4774655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774675 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 6]
def baseStart_4774675 : Nat := 118140960795 + 4774675 * 2 ^ 59
def prefixEnd_4774675 : Nat := 4983230072969 + 3 ^ 40 * 4774675 * 2
def baseEnd_4774675 : Nat := 2451703244006211795804175

theorem tailTrace_4774675 : CollatzResearch.WordTrace tailWord_4774675 prefixEnd_4774675 2451703244006211795804175 := by
  unfold tailWord_4774675
  simp only [CollatzResearch.WordTrace]
  refine ⟨174146703977175399413853479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116097802651450266275902319 174146703977175399413853479)
  ·
    refine ⟨261220055965763099120780219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174146703977175399413853479 261220055965763099120780219)
    ·
      refine ⟨391830083948644648681170329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261220055965763099120780219 391830083948644648681170329)
      ·
        refine ⟨293872562961483486510877747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 391830083948644648681170329 293872562961483486510877747)
        ·
          refine ⟨440808844442225229766316621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293872562961483486510877747 440808844442225229766316621)
          ·
            refine ⟨165303316665834461162368733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 440808844442225229766316621 165303316665834461162368733)
            ·
              refine ⟨61988743749687922935888275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 165303316665834461162368733 61988743749687922935888275)
              ·
                refine ⟨92983115624531884403832413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61988743749687922935888275 92983115624531884403832413)
                ·
                  refine ⟨34868668359199456651437155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92983115624531884403832413 34868668359199456651437155)
                  ·
                    refine ⟨52303002538799184977155733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34868668359199456651437155 52303002538799184977155733)
                    ·
                      refine ⟨2451703244006211795804175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52303002538799184977155733 2451703244006211795804175)
                      ·
                        rfl

theorem cell23_4774675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 6].length) (baseStart_4774675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774675 prefixEnd_4774675 := by exact prefixLift 4774675
  have htrace : WordTrace (prefixWord ++ tailWord_4774675) baseStart_4774675 baseEnd_4774675 := by
    simpa [prefixWord, tailWord_4774675, baseEnd_4774675] using wordTrace_append hprefix tailTrace_4774675
  have hstable : (prefixWord ++ tailWord_4774675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774675).length < 2 ^ (prefixWord ++ tailWord_4774675).sum := by decide
  have hdescent : baseEnd_4774675 < baseStart_4774675 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774682 : List Nat := [3, 1, 1, 3, 2, 1, 1, 4, 1, 1, 5]
def baseStart_4774682 : Nat := 118140960795 + 4774682 * 2 ^ 59
def prefixEnd_4774682 : Nat := 4983230072969 + 3 ^ 40 * 4774682 * 2
def baseEnd_4774682 : Nat := 2451706838370793268416643

theorem tailTrace_4774682 : CollatzResearch.WordTrace tailWord_4774682 prefixEnd_4774682 2451706838370793268416643 := by
  unfold tailWord_4774682
  simp only [CollatzResearch.WordTrace]
  refine ⟨43536739822037509902339575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116097972858766693072905533 43536739822037509902339575)
  ·
    refine ⟨65305109733056264853509363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43536739822037509902339575 65305109733056264853509363)
    ·
      refine ⟨97957664599584397280264045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65305109733056264853509363 97957664599584397280264045)
      ·
        refine ⟨36734124224844148980099017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97957664599584397280264045 36734124224844148980099017)
        ·
          refine ⟨27550593168633111735074263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36734124224844148980099017 27550593168633111735074263)
          ·
            refine ⟨41325889752949667602611395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27550593168633111735074263 41325889752949667602611395)
            ·
              refine ⟨61988834629424501403917093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41325889752949667602611395 61988834629424501403917093)
              ·
                refine ⟨11622906493017094013234455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61988834629424501403917093 11622906493017094013234455)
                ·
                  refine ⟨17434359739525641019851683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11622906493017094013234455 17434359739525641019851683)
                  ·
                    refine ⟨26151539609288461529777525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17434359739525641019851683 26151539609288461529777525)
                    ·
                      refine ⟨2451706838370793268416643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26151539609288461529777525 2451706838370793268416643)
                      ·
                        rfl

theorem cell23_4774682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_4774682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774682 prefixEnd_4774682 := by exact prefixLift 4774682
  have htrace : WordTrace (prefixWord ++ tailWord_4774682) baseStart_4774682 baseEnd_4774682 := by
    simpa [prefixWord, tailWord_4774682, baseEnd_4774682] using wordTrace_append hprefix tailTrace_4774682
  have hstable : (prefixWord ++ tailWord_4774682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774682).length < 2 ^ (prefixWord ++ tailWord_4774682).sum := by decide
  have hdescent : baseEnd_4774682 < baseStart_4774682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774689 : List Nat := [1, 2, 3, 2, 1, 2, 3, 3, 2, 4]
def baseStart_4774689 : Nat := 118140960795 + 4774689 * 2 ^ 59
def prefixEnd_4774689 : Nat := 4983230072969 + 3 ^ 40 * 4774689 * 2
def baseEnd_4774689 : Nat := 817236810911791580343037

theorem tailTrace_4774689 : CollatzResearch.WordTrace tailWord_4774689 prefixEnd_4774689 817236810911791580343037 := by
  unfold tailWord_4774689
  simp only [CollatzResearch.WordTrace]
  refine ⟨174147214599124679804863121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116098143066083119869908747 174147214599124679804863121)
  ·
    refine ⟨130610410949343509853647341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174147214599124679804863121 130610410949343509853647341)
    ·
      refine ⟨48978904106003816195117753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130610410949343509853647341 48978904106003816195117753)
      ·
        refine ⟨36734178079502862146338315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48978904106003816195117753 36734178079502862146338315)
        ·
          refine ⟨55101267119254293219507473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36734178079502862146338315 55101267119254293219507473)
          ·
            refine ⟨41325950339440719914630605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55101267119254293219507473 41325950339440719914630605)
            ·
              refine ⟨15497231377290269967986477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41325950339440719914630605 15497231377290269967986477)
              ·
                refine ⟨5811461766483851237994929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15497231377290269967986477 5811461766483851237994929)
                ·
                  refine ⟨4358596324862888428496197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5811461766483851237994929 4358596324862888428496197)
                  ·
                    refine ⟨817236810911791580343037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4358596324862888428496197 817236810911791580343037)
                    ·
                      rfl

theorem cell23_4774689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 3, 2, 4].length) (baseStart_4774689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774689 prefixEnd_4774689 := by exact prefixLift 4774689
  have htrace : WordTrace (prefixWord ++ tailWord_4774689) baseStart_4774689 baseEnd_4774689 := by
    simpa [prefixWord, tailWord_4774689, baseEnd_4774689] using wordTrace_append hprefix tailTrace_4774689
  have hstable : (prefixWord ++ tailWord_4774689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774689).length < 2 ^ (prefixWord ++ tailWord_4774689).sum := by decide
  have hdescent : baseEnd_4774689 < baseStart_4774689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774696 : List Nat := [2, 1, 5, 1, 1, 1, 2, 1, 5, 2, 2]
def baseStart_4774696 : Nat := 118140960795 + 4774696 * 2 ^ 59
def prefixEnd_4774696 : Nat := 4983230072969 + 3 ^ 40 * 4774696 * 2
def baseEnd_4774696 : Nat := 2451714027099956213641579

theorem tailTrace_4774696 : CollatzResearch.WordTrace tailWord_4774696 prefixEnd_4774696 2451714027099956213641579 := by
  unfold tailWord_4774696
  simp only [CollatzResearch.WordTrace]
  refine ⟨87073734955049660000183971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116098313273399546666911961 87073734955049660000183971)
  ·
    refine ⟨130610602432574490000275957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87073734955049660000183971 130610602432574490000275957)
    ·
      refine ⟨12244743978053858437525871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 130610602432574490000275957 12244743978053858437525871)
      ·
        refine ⟨18367115967080787656288807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12244743978053858437525871 18367115967080787656288807)
        ·
          refine ⟨27550673950621181484433211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18367115967080787656288807 27550673950621181484433211)
          ·
            refine ⟨41326010925931772226649817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27550673950621181484433211 41326010925931772226649817)
            ·
              refine ⟨30994508194448829169987363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41326010925931772226649817 30994508194448829169987363)
              ·
                refine ⟨46491762291673243754981045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30994508194448829169987363 46491762291673243754981045)
                ·
                  refine ⟨4358602714844366602029473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46491762291673243754981045 4358602714844366602029473)
                  ·
                    refine ⟨3268952036133274951522105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4358602714844366602029473 3268952036133274951522105)
                    ·
                      refine ⟨2451714027099956213641579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3268952036133274951522105 2451714027099956213641579)
                      ·
                        rfl

theorem cell23_4774696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_4774696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774696 prefixEnd_4774696 := by exact prefixLift 4774696
  have htrace : WordTrace (prefixWord ++ tailWord_4774696) baseStart_4774696 baseEnd_4774696 := by
    simpa [prefixWord, tailWord_4774696, baseEnd_4774696] using wordTrace_append hprefix tailTrace_4774696
  have hstable : (prefixWord ++ tailWord_4774696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774696).length < 2 ^ (prefixWord ++ tailWord_4774696).sum := by decide
  have hdescent : baseEnd_4774696 < baseStart_4774696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774709 : List Nat := [1, 3, 3, 1, 3, 2, 1, 2, 1, 2, 4]
def baseStart_4774709 : Nat := 118140960795 + 4774709 * 2 ^ 59
def prefixEnd_4774709 : Nat := 4983230072969 + 3 ^ 40 * 4774709 * 2
def baseEnd_4774709 : Nat := 2451720702348464662779019

theorem tailTrace_4774709 : CollatzResearch.WordTrace tailWord_4774709 prefixEnd_4774709 2451720702348464662779019 := by
  unfold tailWord_4774709
  simp only [CollatzResearch.WordTrace]
  refine ⟨174147944059052223220591181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116098629372701482147060787 174147944059052223220591181)
  ·
    refine ⟨65305479022144583707721693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174147944059052223220591181 65305479022144583707721693)
    ·
      refine ⟨24489554633304218890395635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65305479022144583707721693 24489554633304218890395635)
      ·
        refine ⟨36734331949956328335593453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24489554633304218890395635 36734331949956328335593453)
        ·
          refine ⟨13775374481233623125847545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36734331949956328335593453 13775374481233623125847545)
          ·
            refine ⟨10331530860925217344385659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13775374481233623125847545 10331530860925217344385659)
            ·
              refine ⟨15497296291387826016578489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10331530860925217344385659 15497296291387826016578489)
              ·
                refine ⟨11622972218540869512433867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15497296291387826016578489 11622972218540869512433867)
                ·
                  refine ⟨17434458327811304268650801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11622972218540869512433867 17434458327811304268650801)
                  ·
                    refine ⟨13075843745858478201488101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17434458327811304268650801 13075843745858478201488101)
                    ·
                      refine ⟨2451720702348464662779019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13075843745858478201488101 2451720702348464662779019)
                      ·
                        rfl

theorem cell23_4774709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_4774709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774709 prefixEnd_4774709 := by exact prefixLift 4774709
  have htrace : WordTrace (prefixWord ++ tailWord_4774709) baseStart_4774709 baseEnd_4774709 := by
    simpa [prefixWord, tailWord_4774709, baseEnd_4774709] using wordTrace_append hprefix tailTrace_4774709
  have hstable : (prefixWord ++ tailWord_4774709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774709).length < 2 ^ (prefixWord ++ tailWord_4774709).sum := by decide
  have hdescent : baseEnd_4774709 < baseStart_4774709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774724 : List Nat := [2, 3, 4, 2, 1, 2, 2, 2, 1, 1, 3]
def baseStart_4774724 : Nat := 118140960795 + 4774724 * 2 ^ 59
def prefixEnd_4774724 : Nat := 4983230072969 + 3 ^ 40 * 4774724 * 2
def baseEnd_4774724 : Nat := 2451728404558282104091451

theorem tailTrace_4774724 : CollatzResearch.WordTrace tailWord_4774724 prefixEnd_4774724 2451728404558282104091451 := by
  unfold tailWord_4774724
  simp only [CollatzResearch.WordTrace]
  refine ⟨87074245576998940391193613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116098994102665253854924817 87074245576998940391193613)
  ·
    refine ⟨32652842091374602646697605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87074245576998940391193613 32652842091374602646697605)
    ·
      refine ⟨6122407892132737996255801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32652842091374602646697605 6122407892132737996255801)
      ·
        refine ⟨4591805919099553497191851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6122407892132737996255801 4591805919099553497191851)
        ·
          refine ⟨6887708878649330245787777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4591805919099553497191851 6887708878649330245787777)
          ·
            refine ⟨5165781658986997684340833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6887708878649330245787777 5165781658986997684340833)
            ·
              refine ⟨3874336244240248263255625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5165781658986997684340833 3874336244240248263255625)
              ·
                refine ⟨2905752183180186197441719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3874336244240248263255625 2905752183180186197441719)
                ·
                  refine ⟨4358628274770279296162579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2905752183180186197441719 4358628274770279296162579)
                  ·
                    refine ⟨6537942412155418944243869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4358628274770279296162579 6537942412155418944243869)
                    ·
                      refine ⟨2451728404558282104091451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6537942412155418944243869 2451728404558282104091451)
                      ·
                        rfl

theorem cell23_4774724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_4774724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774724 prefixEnd_4774724 := by exact prefixLift 4774724
  have htrace : WordTrace (prefixWord ++ tailWord_4774724) baseStart_4774724 baseEnd_4774724 := by
    simpa [prefixWord, tailWord_4774724, baseEnd_4774724] using wordTrace_append hprefix tailTrace_4774724
  have hstable : (prefixWord ++ tailWord_4774724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774724).length < 2 ^ (prefixWord ++ tailWord_4774724).sum := by decide
  have hdescent : baseEnd_4774724 < baseStart_4774724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774732 : List Nat := [2, 2, 1, 3, 3, 1, 1, 1, 2, 7]
def baseStart_4774732 : Nat := 118140960795 + 4774732 * 2 ^ 59
def prefixEnd_4774732 : Nat := 4983230072969 + 3 ^ 40 * 4774732 * 2
def baseEnd_4774732 : Nat := 817244170801172690930471

theorem tailTrace_4774732 : CollatzResearch.WordTrace tailWord_4774732 prefixEnd_4774732 817244170801172690930471 := by
  unfold tailWord_4774732
  simp only [CollatzResearch.WordTrace]
  refine ⟨87074391468984449074339225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116099188625312598765785633 87074391468984449074339225)
  ·
    refine ⟨65305793601738336805754419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87074391468984449074339225 65305793601738336805754419)
    ·
      refine ⟨97958690402607505208631629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65305793601738336805754419 97958690402607505208631629)
      ·
        refine ⟨36734508900977814453236861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97958690402607505208631629 36734508900977814453236861)
        ·
          refine ⟨13775440837866680419963823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36734508900977814453236861 13775440837866680419963823)
          ·
            refine ⟨20663161256800020629945735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13775440837866680419963823 20663161256800020629945735)
            ·
              refine ⟨30994741885200030944918603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20663161256800020629945735 30994741885200030944918603)
              ·
                refine ⟨46492112827800046417377905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30994741885200030944918603 46492112827800046417377905)
                ·
                  refine ⟨34869084620850034813033429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46492112827800046417377905 34869084620850034813033429)
                  ·
                    refine ⟨817244170801172690930471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34869084620850034813033429 817244170801172690930471)
                    ·
                      rfl

theorem cell23_4774732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 2, 7].length) (baseStart_4774732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774732 prefixEnd_4774732 := by exact prefixLift 4774732
  have htrace : WordTrace (prefixWord ++ tailWord_4774732) baseStart_4774732 baseEnd_4774732 := by
    simpa [prefixWord, tailWord_4774732, baseEnd_4774732] using wordTrace_append hprefix tailTrace_4774732
  have hstable : (prefixWord ++ tailWord_4774732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774732).length < 2 ^ (prefixWord ++ tailWord_4774732).sum := by decide
  have hdescent : baseEnd_4774732 < baseStart_4774732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774746 : List Nat := [3, 1, 1, 2, 1, 4, 2, 3, 2, 1, 3]
def baseStart_4774746 : Nat := 118140960795 + 4774746 * 2 ^ 59
def prefixEnd_4774746 : Nat := 4983230072969 + 3 ^ 40 * 4774746 * 2
def baseEnd_4774746 : Nat := 2451739701132681018016349

theorem tailTrace_4774746 : CollatzResearch.WordTrace tailWord_4774746 prefixEnd_4774746 2451739701132681018016349 := by
  unfold tailWord_4774746
  simp only [CollatzResearch.WordTrace]
  refine ⟨43537323389979544634922023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116099529039945452359792061 43537323389979544634922023)
  ·
    refine ⟨65305985084969316952383035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43537323389979544634922023 65305985084969316952383035)
    ·
      refine ⟨97958977627453975428574553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65305985084969316952383035 97958977627453975428574553)
      ·
        refine ⟨73469233220590481571430915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97958977627453975428574553 73469233220590481571430915)
        ·
          refine ⟨110203849830885722357146373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73469233220590481571430915 110203849830885722357146373)
          ·
            refine ⟨20663221843291072941964945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110203849830885722357146373 20663221843291072941964945)
            ·
              refine ⟨15497416382468304706473709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20663221843291072941964945 15497416382468304706473709)
              ·
                refine ⟨5811531143425614264927641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15497416382468304706473709 5811531143425614264927641)
                ·
                  refine ⟨4358648357569210698695731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5811531143425614264927641 4358648357569210698695731)
                  ·
                    refine ⟨6537972536353816048043597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4358648357569210698695731 6537972536353816048043597)
                    ·
                      refine ⟨2451739701132681018016349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6537972536353816048043597 2451739701132681018016349)
                      ·
                        rfl

theorem cell23_4774746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 3, 2, 1, 3].length) (baseStart_4774746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774746 prefixEnd_4774746 := by exact prefixLift 4774746
  have htrace : WordTrace (prefixWord ++ tailWord_4774746) baseStart_4774746 baseEnd_4774746 := by
    simpa [prefixWord, tailWord_4774746, baseEnd_4774746] using wordTrace_append hprefix tailTrace_4774746
  have hstable : (prefixWord ++ tailWord_4774746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774746).length < 2 ^ (prefixWord ++ tailWord_4774746).sum := by decide
  have hdescent : baseEnd_4774746 < baseStart_4774746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774752 : List Nat := [2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 4]
def baseStart_4774752 : Nat := 118140960795 + 4774752 * 2 ^ 59
def prefixEnd_4774752 : Nat := 4983230072969 + 3 ^ 40 * 4774752 * 2
def baseEnd_4774752 : Nat := 2451742782016607994541321

theorem tailTrace_4774752 : CollatzResearch.WordTrace tailWord_4774752 prefixEnd_4774752 2451742782016607994541321 := by
  unfold tailWord_4774752
  simp only [CollatzResearch.WordTrace]
  refine ⟨87074756198948220782203255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116099674931930961042937673 87074756198948220782203255)
  ·
    refine ⟨130612134298422331173304883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87074756198948220782203255 130612134298422331173304883)
    ·
      refine ⟨195918201447633496759957325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130612134298422331173304883 195918201447633496759957325)
      ·
        refine ⟨73469325542862561284983997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195918201447633496759957325 73469325542862561284983997)
        ·
          refine ⟨27550997078573460481868999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73469325542862561284983997 27550997078573460481868999)
          ·
            refine ⟨41326495617860190722803499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27550997078573460481868999 41326495617860190722803499)
            ·
              refine ⟨61989743426790286084205249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41326495617860190722803499 61989743426790286084205249)
              ·
                refine ⟨46492307570092714563153937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61989743426790286084205249 46492307570092714563153937)
                ·
                  refine ⟨34869230677569535922365453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46492307570092714563153937 34869230677569535922365453)
                  ·
                    refine ⟨13075961504088575970887045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34869230677569535922365453 13075961504088575970887045)
                    ·
                      refine ⟨2451742782016607994541321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13075961504088575970887045 2451742782016607994541321)
                      ·
                        rfl

theorem cell23_4774752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_4774752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774752 prefixEnd_4774752 := by exact prefixLift 4774752
  have htrace : WordTrace (prefixWord ++ tailWord_4774752) baseStart_4774752 baseEnd_4774752 := by
    simpa [prefixWord, tailWord_4774752, baseEnd_4774752] using wordTrace_append hprefix tailTrace_4774752
  have hstable : (prefixWord ++ tailWord_4774752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774752).length < 2 ^ (prefixWord ++ tailWord_4774752).sum := by decide
  have hdescent : baseEnd_4774752 < baseStart_4774752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774756 : List Nat := [2, 3, 1, 1, 4, 1, 2, 1, 3, 3, 2]
def baseStart_4774756 : Nat := 118140960795 + 4774756 * 2 ^ 59
def prefixEnd_4774756 : Nat := 4983230072969 + 3 ^ 40 * 4774756 * 2
def baseEnd_4774756 : Nat := 2451744835939225978891303

theorem tailTrace_4774756 : CollatzResearch.WordTrace tailWord_4774756 prefixEnd_4774756 2451744835939225978891303 := by
  unfold tailWord_4774756
  simp only [CollatzResearch.WordTrace]
  refine ⟨87074829144940975123776061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116099772193254633498368081 87074829144940975123776061)
  ·
    refine ⟨32653060929352865671416023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87074829144940975123776061 32653060929352865671416023)
    ·
      refine ⟨48979591394029298507124035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32653060929352865671416023 48979591394029298507124035)
      ·
        refine ⟨73469387091043947760686053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48979591394029298507124035 73469387091043947760686053)
        ·
          refine ⟨13775510079570740205128635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73469387091043947760686053 13775510079570740205128635)
          ·
            refine ⟨20663265119356110307692953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13775510079570740205128635 20663265119356110307692953)
            ·
              refine ⟨15497448839517082730769715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20663265119356110307692953 15497448839517082730769715)
              ·
                refine ⟨23246173259275624096154573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15497448839517082730769715 23246173259275624096154573)
                ·
                  refine ⟨8717314972228359036057965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23246173259275624096154573 8717314972228359036057965)
                  ·
                    refine ⟨3268993114585634638521737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8717314972228359036057965 3268993114585634638521737)
                    ·
                      refine ⟨2451744835939225978891303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3268993114585634638521737 2451744835939225978891303)
                      ·
                        rfl

theorem cell23_4774756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 3, 3, 2].length) (baseStart_4774756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774756 prefixEnd_4774756 := by exact prefixLift 4774756
  have htrace : WordTrace (prefixWord ++ tailWord_4774756) baseStart_4774756 baseEnd_4774756 := by
    simpa [prefixWord, tailWord_4774756, baseEnd_4774756] using wordTrace_append hprefix tailTrace_4774756
  have hstable : (prefixWord ++ tailWord_4774756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774756).length < 2 ^ (prefixWord ++ tailWord_4774756).sum := by decide
  have hdescent : baseEnd_4774756 < baseStart_4774756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774773 : List Nat := [1, 3, 4, 1, 1, 3, 1, 3, 1, 3, 2]
def baseStart_4774773 : Nat := 118140960795 + 4774773 * 2 ^ 59
def prefixEnd_4774773 : Nat := 4983230072969 + 3 ^ 40 * 4774773 * 2
def baseEnd_4774773 : Nat := 2451753565110352412378725

theorem tailTrace_4774773 : CollatzResearch.WordTrace tailWord_4774773 prefixEnd_4774773 2451753565110352412378725 := by
  unfold tailWord_4774773
  simp only [CollatzResearch.WordTrace]
  refine ⟨174150278330820362150920973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116100185553880241433947315 174150278330820362150920973)
  ·
    refine ⟨65306354374057635806595365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174150278330820362150920973 65306354374057635806595365)
    ·
      refine ⟨12244941445135806713736631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65306354374057635806595365 12244941445135806713736631)
      ·
        refine ⟨18367412167703710070604947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12244941445135806713736631 18367412167703710070604947)
        ·
          refine ⟨27551118251555565105907421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18367412167703710070604947 27551118251555565105907421)
          ·
            refine ⟨10331669344333336914715283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27551118251555565105907421 10331669344333336914715283)
            ·
              refine ⟨15497504016500005372072925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10331669344333336914715283 15497504016500005372072925)
              ·
                refine ⟨5811564006187502014527347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15497504016500005372072925 5811564006187502014527347)
                ·
                  refine ⟨8717346009281253021791021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5811564006187502014527347 8717346009281253021791021)
                  ·
                    refine ⟨3269004753480469883171633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8717346009281253021791021 3269004753480469883171633)
                    ·
                      refine ⟨2451753565110352412378725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3269004753480469883171633 2451753565110352412378725)
                      ·
                        rfl

theorem cell23_4774773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_4774773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774773 prefixEnd_4774773 := by exact prefixLift 4774773
  have htrace : WordTrace (prefixWord ++ tailWord_4774773) baseStart_4774773 baseEnd_4774773 := by
    simpa [prefixWord, tailWord_4774773, baseEnd_4774773] using wordTrace_append hprefix tailTrace_4774773
  have hstable : (prefixWord ++ tailWord_4774773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774773).length < 2 ^ (prefixWord ++ tailWord_4774773).sum := by decide
  have hdescent : baseEnd_4774773 < baseStart_4774773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774846 : List Nat := [4, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2]
def baseStart_4774846 : Nat := 118140960795 + 4774846 * 2 ^ 59
def prefixEnd_4774846 : Nat := 4983230072969 + 3 ^ 40 * 4774846 * 2
def baseEnd_4774846 : Nat := 2451791049198130626765889

theorem tailTrace_4774846 : CollatzResearch.WordTrace tailWord_4774846 prefixEnd_4774846 2451791049198130626765889 := by
  unfold tailWord_4774846
  simp only [CollatzResearch.WordTrace]
  refine ⟨21769117607444486952291049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116101960573037263745552261 21769117607444486952291049)
  ·
    refine ⟨16326838205583365214218287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21769117607444486952291049 16326838205583365214218287)
    ·
      refine ⟨24490257308375047821327431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16326838205583365214218287 24490257308375047821327431)
      ·
        refine ⟨36735385962562571731991147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24490257308375047821327431 36735385962562571731991147)
        ·
          refine ⟨55103078943843857597986721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36735385962562571731991147 55103078943843857597986721)
          ·
            refine ⟨41327309207882893198490041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55103078943843857597986721 41327309207882893198490041)
            ·
              refine ⟨30995481905912169898867531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41327309207882893198490041 30995481905912169898867531)
              ·
                refine ⟨46493222858868254848301297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30995481905912169898867531 46493222858868254848301297)
                ·
                  refine ⟨34869917144151191136225973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46493222858868254848301297 34869917144151191136225973)
                  ·
                    refine ⟨3269054732264174169021185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34869917144151191136225973 3269054732264174169021185)
                    ·
                      refine ⟨2451791049198130626765889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3269054732264174169021185 2451791049198130626765889)
                      ·
                        rfl

theorem cell23_4774846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2].length) (baseStart_4774846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774846 prefixEnd_4774846 := by exact prefixLift 4774846
  have htrace : WordTrace (prefixWord ++ tailWord_4774846) baseStart_4774846 baseEnd_4774846 := by
    simpa [prefixWord, tailWord_4774846, baseEnd_4774846] using wordTrace_append hprefix tailTrace_4774846
  have hstable : (prefixWord ++ tailWord_4774846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774846).length < 2 ^ (prefixWord ++ tailWord_4774846).sum := by decide
  have hdescent : baseEnd_4774846 < baseStart_4774846 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774909 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 2, 5, 3]
def baseStart_4774909 : Nat := 118140960795 + 4774909 * 2 ^ 59
def prefixEnd_4774909 : Nat := 4983230072969 + 3 ^ 40 * 4774909 * 2
def baseEnd_4774909 : Nat := 2451823398479363880278099

theorem tailTrace_4774909 : CollatzResearch.WordTrace tailWord_4774909 prefixEnd_4774909 2451823398479363880278099 := by
  unfold tailWord_4774909
  simp only [CollatzResearch.WordTrace]
  refine ⟨174155238658327657377871781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116103492438885104918581187 174155238658327657377871781)
  ·
    refine ⟨32654107248436435758350959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174155238658327657377871781 32654107248436435758350959)
    ·
      refine ⟨48981160872654653637526439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32654107248436435758350959 48981160872654653637526439)
      ·
        refine ⟨73471741308981980456289659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48981160872654653637526439 73471741308981980456289659)
        ·
          refine ⟨110207611963472970684434489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73471741308981980456289659 110207611963472970684434489)
          ·
            refine ⟨82655708972604728013325867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110207611963472970684434489 82655708972604728013325867)
            ·
              refine ⟨123983563458907092019988801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82655708972604728013325867 123983563458907092019988801)
              ·
                refine ⟨92987672594180319014991601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123983563458907092019988801 92987672594180319014991601)
                ·
                  refine ⟨69740754445635239261243701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92987672594180319014991601 69740754445635239261243701)
                  ·
                    refine ⟨6538195729278303680741597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 69740754445635239261243701 6538195729278303680741597)
                    ·
                      refine ⟨2451823398479363880278099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6538195729278303680741597 2451823398479363880278099)
                      ·
                        rfl

theorem cell23_4774909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 5, 3].length) (baseStart_4774909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774909 prefixEnd_4774909 := by exact prefixLift 4774909
  have htrace : WordTrace (prefixWord ++ tailWord_4774909) baseStart_4774909 baseEnd_4774909 := by
    simpa [prefixWord, tailWord_4774909, baseEnd_4774909] using wordTrace_append hprefix tailTrace_4774909
  have hstable : (prefixWord ++ tailWord_4774909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774909).length < 2 ^ (prefixWord ++ tailWord_4774909).sum := by decide
  have hdescent : baseEnd_4774909 < baseStart_4774909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774910 : List Nat := [4, 2, 2, 2, 2, 1, 1, 1, 2, 4, 2]
def baseStart_4774910 : Nat := 118140960795 + 4774910 * 2 ^ 59
def prefixEnd_4774910 : Nat := 4983230072969 + 3 ^ 40 * 4774910 * 2
def baseEnd_4774910 : Nat := 2451823911960018376365595

theorem tailTrace_4774910 : CollatzResearch.WordTrace tailWord_4774910 prefixEnd_4774910 2451823911960018376365595 := by
  unfold tailWord_4774910
  simp only [CollatzResearch.WordTrace]
  refine ⟨21769409391415504318582273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116103516754216023032438789 21769409391415504318582273)
  ·
    refine ⟨16327057043561628238936705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21769409391415504318582273 16327057043561628238936705)
    ·
      refine ⟨12245292782671221179202529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16327057043561628238936705 12245292782671221179202529)
      ·
        refine ⟨9183969587003415884401897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12245292782671221179202529 9183969587003415884401897)
        ·
          refine ⟨6887977190252561913301423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9183969587003415884401897 6887977190252561913301423)
          ·
            refine ⟨10331965785378842869952135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6887977190252561913301423 10331965785378842869952135)
            ·
              refine ⟨15497948678068264304928203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10331965785378842869952135 15497948678068264304928203)
              ·
                refine ⟨23246923017102396457392305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15497948678068264304928203 23246923017102396457392305)
                ·
                  refine ⟨17435192262826797343044229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23246923017102396457392305 17435192262826797343044229)
                  ·
                    refine ⟨3269098549280024501820793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17435192262826797343044229 3269098549280024501820793)
                    ·
                      refine ⟨2451823911960018376365595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3269098549280024501820793 2451823911960018376365595)
                      ·
                        rfl

theorem cell23_4774910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_4774910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774910 prefixEnd_4774910 := by exact prefixLift 4774910
  have htrace : WordTrace (prefixWord ++ tailWord_4774910) baseStart_4774910 baseEnd_4774910 := by
    simpa [prefixWord, tailWord_4774910, baseEnd_4774910] using wordTrace_append hprefix tailTrace_4774910
  have hstable : (prefixWord ++ tailWord_4774910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774910).length < 2 ^ (prefixWord ++ tailWord_4774910).sum := by decide
  have hdescent : baseEnd_4774910 < baseStart_4774910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774979 : List Nat := [1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 6]
def baseStart_4774979 : Nat := 118140960795 + 4774979 * 2 ^ 59
def prefixEnd_4774979 : Nat := 4983230072969 + 3 ^ 40 * 4774979 * 2
def baseEnd_4774979 : Nat := 2451859342125178606402777

theorem tailTrace_4774979 : CollatzResearch.WordTrace tailWord_4774979 prefixEnd_4774979 2451859342125178606402777 := by
  unfold tailWord_4774979
  simp only [CollatzResearch.WordTrace]
  refine ⟨174157791768074059332919991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116105194512049372888613327 174157791768074059332919991)
  ·
    refine ⟨261236687652111088999379987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174157791768074059332919991 261236687652111088999379987)
    ·
      refine ⟨391855031478166633499069981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261236687652111088999379987 391855031478166633499069981)
      ·
        refine ⟨146945636804312487562151243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 391855031478166633499069981 146945636804312487562151243)
        ·
          refine ⟨220418455206468731343226865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146945636804312487562151243 220418455206468731343226865)
          ·
            refine ⟨165313841404851548507420149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220418455206468731343226865 165313841404851548507420149)
            ·
              refine ⟨15498172631704832672570639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 165313841404851548507420149 15498172631704832672570639)
              ·
                refine ⟨23247258947557249008855959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15498172631704832672570639 23247258947557249008855959)
                ·
                  refine ⟨34870888421335873513283939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23247258947557249008855959 34870888421335873513283939)
                  ·
                    refine ⟨52306332632003810269925909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34870888421335873513283939 52306332632003810269925909)
                    ·
                      refine ⟨2451859342125178606402777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52306332632003810269925909 2451859342125178606402777)
                      ·
                        rfl

theorem cell23_4774979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 6].length) (baseStart_4774979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774979 prefixEnd_4774979 := by exact prefixLift 4774979
  have htrace : WordTrace (prefixWord ++ tailWord_4774979) baseStart_4774979 baseEnd_4774979 := by
    simpa [prefixWord, tailWord_4774979, baseEnd_4774979] using wordTrace_append hprefix tailTrace_4774979
  have hstable : (prefixWord ++ tailWord_4774979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774979).length < 2 ^ (prefixWord ++ tailWord_4774979).sum := by decide
  have hdescent : baseEnd_4774979 < baseStart_4774979 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774983 : List Nat := [1, 1, 4, 1, 3, 3, 2, 2, 1, 1, 4]
def baseStart_4774983 : Nat := 118140960795 + 4774983 * 2 ^ 59
def prefixEnd_4774983 : Nat := 4983230072969 + 3 ^ 40 * 4774983 * 2
def baseEnd_4774983 : Nat := 2451861396047796590752759

theorem tailTrace_4774983 : CollatzResearch.WordTrace tailWord_4774983 prefixEnd_4774983 2451861396047796590752759 := by
  unfold tailWord_4774983
  simp only [CollatzResearch.WordTrace]
  refine ⟨174157937660059568016065603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116105291773373045344043735 174157937660059568016065603)
  ·
    refine ⟨261236906490089352024098405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174157937660059568016065603 261236906490089352024098405)
    ·
      refine ⟨48981919966891753504518451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 261236906490089352024098405 48981919966891753504518451)
      ·
        refine ⟨73472879950337630256777677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48981919966891753504518451 73472879950337630256777677)
        ·
          refine ⟨27552329981376611346291629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73472879950337630256777677 27552329981376611346291629)
          ·
            refine ⟨10332123743016229254859361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27552329981376611346291629 10332123743016229254859361)
            ·
              refine ⟨7749092807262171941144521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10332123743016229254859361 7749092807262171941144521)
              ·
                refine ⟨5811819605446628955858391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7749092807262171941144521 5811819605446628955858391)
                ·
                  refine ⟨8717729408169943433787587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5811819605446628955858391 8717729408169943433787587)
                  ·
                    refine ⟨13076594112254915150681381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8717729408169943433787587 13076594112254915150681381)
                    ·
                      refine ⟨2451861396047796590752759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13076594112254915150681381 2451861396047796590752759)
                      ·
                        rfl

theorem cell23_4774983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 2, 1, 1, 4].length) (baseStart_4774983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774983 prefixEnd_4774983 := by exact prefixLift 4774983
  have htrace : WordTrace (prefixWord ++ tailWord_4774983) baseStart_4774983 baseEnd_4774983 := by
    simpa [prefixWord, tailWord_4774983, baseEnd_4774983] using wordTrace_append hprefix tailTrace_4774983
  have hstable : (prefixWord ++ tailWord_4774983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774983).length < 2 ^ (prefixWord ++ tailWord_4774983).sum := by decide
  have hdescent : baseEnd_4774983 < baseStart_4774983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774986 : List Nat := [3, 1, 2, 1, 1, 2, 2, 3, 3, 2, 3]
def baseStart_4774986 : Nat := 118140960795 + 4774986 * 2 ^ 59
def prefixEnd_4774986 : Nat := 4983230072969 + 3 ^ 40 * 4774986 * 2
def baseEnd_4774986 : Nat := 2451862936489760079015245

theorem tailTrace_4774986 : CollatzResearch.WordTrace tailWord_4774986 prefixEnd_4774986 2451862936489760079015245 := by
  unfold tailWord_4774986
  simp only [CollatzResearch.WordTrace]
  refine ⟨43539511769762174882106203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116105364719365799685616541 43539511769762174882106203)
  ·
    refine ⟨65309267654643262323159305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43539511769762174882106203 65309267654643262323159305)
    ·
      refine ⟨48981950740982446742369479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65309267654643262323159305 48981950740982446742369479)
      ·
        refine ⟨73472926111473670113554219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48981950740982446742369479 73472926111473670113554219)
        ·
          refine ⟨110209389167210505170331329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73472926111473670113554219 110209389167210505170331329)
          ·
            refine ⟨82657041875407878877748497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110209389167210505170331329 82657041875407878877748497)
            ·
              refine ⟨61992781406555909158311373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82657041875407878877748497 61992781406555909158311373)
              ·
                refine ⟨23247293027458465934366765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61992781406555909158311373 23247293027458465934366765)
                ·
                  refine ⟨8717734885296924725387537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23247293027458465934366765 8717734885296924725387537)
                  ·
                    refine ⟨6538301163972693544040653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8717734885296924725387537 6538301163972693544040653)
                    ·
                      refine ⟨2451862936489760079015245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6538301163972693544040653 2451862936489760079015245)
                      ·
                        rfl

theorem cell23_4774986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 3, 2, 3].length) (baseStart_4774986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774986 prefixEnd_4774986 := by exact prefixLift 4774986
  have htrace : WordTrace (prefixWord ++ tailWord_4774986) baseStart_4774986 baseEnd_4774986 := by
    simpa [prefixWord, tailWord_4774986, baseEnd_4774986] using wordTrace_append hprefix tailTrace_4774986
  have hstable : (prefixWord ++ tailWord_4774986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774986).length < 2 ^ (prefixWord ++ tailWord_4774986).sum := by decide
  have hdescent : baseEnd_4774986 < baseStart_4774986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4774996 : List Nat := [2, 4, 1, 1, 1, 1, 2, 4, 1, 2, 4]
def baseStart_4774996 : Nat := 118140960795 + 4774996 * 2 ^ 59
def prefixEnd_4774996 : Nat := 4983230072969 + 3 ^ 40 * 4774996 * 2
def baseEnd_4774996 : Nat := 2451868071296305039890199

theorem tailTrace_4774996 : CollatzResearch.WordTrace tailWord_4774996 prefixEnd_4774996 2451868071296305039890199 := by
  unfold tailWord_4774996
  simp only [CollatzResearch.WordTrace]
  refine ⟨87079205904506235618144421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116105607872674980824192561 87079205904506235618144421)
  ·
    refine ⟨16327351107094919178402079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87079205904506235618144421 16327351107094919178402079)
    ·
      refine ⟨24491026660642378767603119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16327351107094919178402079 24491026660642378767603119)
      ·
        refine ⟨36736539990963568151404679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24491026660642378767603119 36736539990963568151404679)
        ·
          refine ⟨55104809986445352227107019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36736539990963568151404679 55104809986445352227107019)
          ·
            refine ⟨82657214979668028340660529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55104809986445352227107019 82657214979668028340660529)
            ·
              refine ⟨61992911234751021255495397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82657214979668028340660529 61992911234751021255495397)
              ·
                refine ⟨11623670856515816485405387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61992911234751021255495397 11623670856515816485405387)
                ·
                  refine ⟨17435506284773724728108081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11623670856515816485405387 17435506284773724728108081)
                  ·
                    refine ⟨13076629713580293546081061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17435506284773724728108081 13076629713580293546081061)
                    ·
                      refine ⟨2451868071296305039890199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13076629713580293546081061 2451868071296305039890199)
                      ·
                        rfl

theorem cell23_4774996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_4774996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4774996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4774996 prefixEnd_4774996 := by exact prefixLift 4774996
  have htrace : WordTrace (prefixWord ++ tailWord_4774996) baseStart_4774996 baseEnd_4774996 := by
    simpa [prefixWord, tailWord_4774996, baseEnd_4774996] using wordTrace_append hprefix tailTrace_4774996
  have hstable : (prefixWord ++ tailWord_4774996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4774996).length < 2 ^ (prefixWord ++ tailWord_4774996).sum := by decide
  have hdescent : baseEnd_4774996 < baseStart_4774996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4774996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775043 : List Nat := [1, 1, 1, 3, 3, 2, 3, 1, 3, 3, 2]
def baseStart_4775043 : Nat := 118140960795 + 4775043 * 2 ^ 59
def prefixEnd_4775043 : Nat := 4983230072969 + 3 ^ 40 * 4775043 * 2
def baseEnd_4775043 : Nat := 2451892204887066356002483

theorem tailTrace_4775043 : CollatzResearch.WordTrace tailWord_4775043 prefixEnd_4775043 2451892204887066356002483 := by
  unfold tailWord_4775043
  simp only [CollatzResearch.WordTrace]
  refine ⟨174160126039842198263249783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116106750693228132175499855 174160126039842198263249783)
  ·
    refine ⟨261240189059763297394874675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174160126039842198263249783 261240189059763297394874675)
    ·
      refine ⟨391860283589644946092312013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261240189059763297394874675 391860283589644946092312013)
      ·
        refine ⟨146947606346116854784617005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 391860283589644946092312013 146947606346116854784617005)
        ·
          refine ⟨55105352379793820544231377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146947606346116854784617005 55105352379793820544231377)
          ·
            refine ⟨41329014284845365408173533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55105352379793820544231377 41329014284845365408173533)
            ·
              refine ⟨15498380356817012028065075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41329014284845365408173533 15498380356817012028065075)
              ·
                refine ⟨23247570535225518042097613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15498380356817012028065075 23247570535225518042097613)
                ·
                  refine ⟨8717838950709569265786605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23247570535225518042097613 8717838950709569265786605)
                  ·
                    refine ⟨3269189606516088474669977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8717838950709569265786605 3269189606516088474669977)
                    ·
                      refine ⟨2451892204887066356002483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3269189606516088474669977 2451892204887066356002483)
                      ·
                        rfl

theorem cell23_4775043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 3, 3, 2].length) (baseStart_4775043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775043 prefixEnd_4775043 := by exact prefixLift 4775043
  have htrace : WordTrace (prefixWord ++ tailWord_4775043) baseStart_4775043 baseEnd_4775043 := by
    simpa [prefixWord, tailWord_4775043, baseEnd_4775043] using wordTrace_append hprefix tailTrace_4775043
  have hstable : (prefixWord ++ tailWord_4775043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775043).length < 2 ^ (prefixWord ++ tailWord_4775043).sum := by decide
  have hdescent : baseEnd_4775043 < baseStart_4775043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775073 : List Nat := [1, 2, 3, 3, 1, 1, 1, 2, 3, 4, 2]
def baseStart_4775073 : Nat := 118140960795 + 4775073 * 2 ^ 59
def prefixEnd_4775073 : Nat := 4983230072969 + 3 ^ 40 * 4775073 * 2
def baseEnd_4775073 : Nat := 2451907609306701238627345

theorem tailTrace_4775073 : CollatzResearch.WordTrace tailWord_4775073 prefixEnd_4775073 2451907609306701238627345 := by
  unfold tailWord_4775073
  simp only [CollatzResearch.WordTrace]
  refine ⟨174161220229733513386841873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116107480153155675591227915 174161220229733513386841873)
  ·
    refine ⟨130620915172300135040131405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174161220229733513386841873 130620915172300135040131405)
    ·
      refine ⟨48982843189612550640049277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130620915172300135040131405 48982843189612550640049277)
      ·
        refine ⟨18368566196104706490018479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48982843189612550640049277 18368566196104706490018479)
        ·
          refine ⟨27552849294157059735027719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18368566196104706490018479 27552849294157059735027719)
          ·
            refine ⟨41329273941235589602541579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27552849294157059735027719 41329273941235589602541579)
            ·
              refine ⟨61993910911853384403812369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41329273941235589602541579 61993910911853384403812369)
              ·
                refine ⟨46495433183890038302859277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61993910911853384403812369 46495433183890038302859277)
                ·
                  refine ⟨17435787443958764363572229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46495433183890038302859277 17435787443958764363572229)
                  ·
                    refine ⟨3269210145742268318169793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17435787443958764363572229 3269210145742268318169793)
                    ·
                      refine ⟨2451907609306701238627345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3269210145742268318169793 2451907609306701238627345)
                      ·
                        rfl

theorem cell23_4775073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_4775073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775073 prefixEnd_4775073 := by exact prefixLift 4775073
  have htrace : WordTrace (prefixWord ++ tailWord_4775073) baseStart_4775073 baseEnd_4775073 := by
    simpa [prefixWord, tailWord_4775073, baseEnd_4775073] using wordTrace_append hprefix tailTrace_4775073
  have hstable : (prefixWord ++ tailWord_4775073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775073).length < 2 ^ (prefixWord ++ tailWord_4775073).sum := by decide
  have hdescent : baseEnd_4775073 < baseStart_4775073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775090 : List Nat := [3, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2]
def baseStart_4775090 : Nat := 118140960795 + 4775090 * 2 ^ 59
def prefixEnd_4775090 : Nat := 4983230072969 + 3 ^ 40 * 4775090 * 2
def baseEnd_4775090 : Nat := 2451916338477827672114767

theorem tailTrace_4775090 : CollatzResearch.WordTrace tailWord_4775090 prefixEnd_4775090 2451916338477827672114767 := by
  unfold tailWord_4775090
  simp only [CollatzResearch.WordTrace]
  refine ⟨43540460067667981322552681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116107893513781283526807149 43540460067667981322552681)
  ·
    refine ⟨32655345050750985991914511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43540460067667981322552681 32655345050750985991914511)
    ·
      refine ⟨48983017576126478987871767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32655345050750985991914511 48983017576126478987871767)
      ·
        refine ⟨73474526364189718481807651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48983017576126478987871767 73474526364189718481807651)
        ·
          refine ⟨110211789546284577722711477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73474526364189718481807651 110211789546284577722711477)
          ·
            refine ⟨10332355269964179161504201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 110211789546284577722711477 10332355269964179161504201)
            ·
              refine ⟨7749266452473134371128151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10332355269964179161504201 7749266452473134371128151)
              ·
                refine ⟨11623899678709701556692227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7749266452473134371128151 11623899678709701556692227)
                ·
                  refine ⟨17435849518064552335038341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11623899678709701556692227 17435849518064552335038341)
                  ·
                    refine ⟨3269221784637103562819689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17435849518064552335038341 3269221784637103562819689)
                    ·
                      refine ⟨2451916338477827672114767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3269221784637103562819689 2451916338477827672114767)
                      ·
                        rfl

theorem cell23_4775090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2].length) (baseStart_4775090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775090 prefixEnd_4775090 := by exact prefixLift 4775090
  have htrace : WordTrace (prefixWord ++ tailWord_4775090) baseStart_4775090 baseEnd_4775090 := by
    simpa [prefixWord, tailWord_4775090, baseEnd_4775090] using wordTrace_append hprefix tailTrace_4775090
  have hstable : (prefixWord ++ tailWord_4775090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775090).length < 2 ^ (prefixWord ++ tailWord_4775090).sum := by decide
  have hdescent : baseEnd_4775090 < baseStart_4775090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775124 : List Nat := [2, 4, 1, 4, 1, 1, 1, 1, 4, 2, 2]
def baseStart_4775124 : Nat := 118140960795 + 4775124 * 2 ^ 59
def prefixEnd_4775124 : Nat := 4983230072969 + 3 ^ 40 * 4775124 * 2
def baseEnd_4775124 : Nat := 2451933796820080539089611

theorem tailTrace_4775124 : CollatzResearch.WordTrace tailWord_4775124 prefixEnd_4775124 2451933796820080539089611 := by
  unfold tailWord_4775124
  simp only [CollatzResearch.WordTrace]
  refine ⟨87081540176274374548474213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116108720235032499397965617 87081540176274374548474213)
  ·
    refine ⟨16327788783051445227838915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87081540176274374548474213 16327788783051445227838915)
    ·
      refine ⟨24491683174577167841758373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16327788783051445227838915 24491683174577167841758373)
      ·
        refine ⟨4592190595233218970329695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24491683174577167841758373 4592190595233218970329695)
        ·
          refine ⟨6888285892849828455494543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4592190595233218970329695 6888285892849828455494543)
          ·
            refine ⟨10332428839274742683241815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6888285892849828455494543 10332428839274742683241815)
            ·
              refine ⟨15498643258912114024862723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10332428839274742683241815 15498643258912114024862723)
              ·
                refine ⟨23247964888368171037294085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15498643258912114024862723 23247964888368171037294085)
                ·
                  refine ⟨4358993416569032069492641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23247964888368171037294085 4358993416569032069492641)
                  ·
                    refine ⟨3269245062426774052119481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4358993416569032069492641 3269245062426774052119481)
                    ·
                      refine ⟨2451933796820080539089611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3269245062426774052119481 2451933796820080539089611)
                      ·
                        rfl

theorem cell23_4775124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_4775124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775124 prefixEnd_4775124 := by exact prefixLift 4775124
  have htrace : WordTrace (prefixWord ++ tailWord_4775124) baseStart_4775124 baseEnd_4775124 := by
    simpa [prefixWord, tailWord_4775124, baseEnd_4775124] using wordTrace_append hprefix tailTrace_4775124
  have hstable : (prefixWord ++ tailWord_4775124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775124).length < 2 ^ (prefixWord ++ tailWord_4775124).sum := by decide
  have hdescent : baseEnd_4775124 < baseStart_4775124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775203 : List Nat := [1, 1, 1, 4, 2, 4, 1, 3, 6]
def baseStart_4775203 : Nat := 118140960795 + 4775203 * 2 ^ 59
def prefixEnd_4775203 : Nat := 4983230072969 + 3 ^ 40 * 4775203 * 2
def baseEnd_4775203 : Nat := 272441595754642858889083

theorem tailTrace_4775203 : CollatzResearch.WordTrace tailWord_4775203 prefixEnd_4775203 272441595754642858889083 := by
  unfold tailWord_4775203
  simp only [CollatzResearch.WordTrace]
  refine ⟨174165961719262545589074263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116110641146175030392716175 174165961719262545589074263)
  ·
    refine ⟨261248942578893818383611395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174165961719262545589074263 261248942578893818383611395)
    ·
      refine ⟨391873413868340727575417093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261248942578893818383611395 391873413868340727575417093)
      ·
        refine ⟨73476265100313886420390705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 391873413868340727575417093 73476265100313886420390705)
        ·
          refine ⟨55107198825235414815293029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73476265100313886420390705 55107198825235414815293029)
          ·
            refine ⟨10332599779731640277867443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55107198825235414815293029 10332599779731640277867443)
            ·
              refine ⟨15498899669597460416801165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10332599779731640277867443 15498899669597460416801165)
              ·
                refine ⟨5812087376099047656300437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15498899669597460416801165 5812087376099047656300437)
                ·
                  refine ⟨272441595754642858889083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5812087376099047656300437 272441595754642858889083)
                  ·
                    rfl

theorem cell23_4775203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 3, 6].length) (baseStart_4775203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775203 prefixEnd_4775203 := by exact prefixLift 4775203
  have htrace : WordTrace (prefixWord ++ tailWord_4775203) baseStart_4775203 baseEnd_4775203 := by
    simpa [prefixWord, tailWord_4775203, baseEnd_4775203] using wordTrace_append hprefix tailTrace_4775203
  have hstable : (prefixWord ++ tailWord_4775203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775203).length < 2 ^ (prefixWord ++ tailWord_4775203).sum := by decide
  have hdescent : baseEnd_4775203 < baseStart_4775203 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775263 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 6, 4]
def baseStart_4775263 : Nat := 118140960795 + 4775263 * 2 ^ 59
def prefixEnd_4775263 : Nat := 4983230072969 + 3 ^ 40 * 4775263 * 2
def baseEnd_4775263 : Nat := 817335056877018498417157

theorem tailTrace_4775263 : CollatzResearch.WordTrace tailWord_4775263 prefixEnd_4775263 817335056877018498417157 := by
  unfold tailWord_4775263
  simp only [CollatzResearch.WordTrace]
  refine ⟨174168150099045175836258443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116112100066030117224172295 174168150099045175836258443)
  ·
    refine ⟨261252225148567763754387665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174168150099045175836258443 261252225148567763754387665)
    ·
      refine ⟨195939168861425822815790749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261252225148567763754387665 195939168861425822815790749)
      ·
        refine ⟨73477188323034683555921531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195939168861425822815790749 73477188323034683555921531)
        ·
          refine ⟨110215782484552025333882297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73477188323034683555921531 110215782484552025333882297)
          ·
            refine ⟨82661836863414019000411723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110215782484552025333882297 82661836863414019000411723)
            ·
              refine ⟨123992755295121028500617585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82661836863414019000411723 123992755295121028500617585)
              ·
                refine ⟨92994566471340771375463189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123992755295121028500617585 92994566471340771375463189)
                ·
                  refine ⟨4359120303344098658224837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 92994566471340771375463189 4359120303344098658224837)
                  ·
                    refine ⟨817335056877018498417157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4359120303344098658224837 817335056877018498417157)
                    ·
                      rfl

theorem cell23_4775263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 6, 4].length) (baseStart_4775263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775263 prefixEnd_4775263 := by exact prefixLift 4775263
  have htrace : WordTrace (prefixWord ++ tailWord_4775263) baseStart_4775263 baseEnd_4775263 := by
    simpa [prefixWord, tailWord_4775263, baseEnd_4775263] using wordTrace_append hprefix tailTrace_4775263
  have hstable : (prefixWord ++ tailWord_4775263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775263).length < 2 ^ (prefixWord ++ tailWord_4775263).sum := by decide
  have hdescent : baseEnd_4775263 < baseStart_4775263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775290 : List Nat := [3, 1, 1, 1, 1, 1, 2, 7, 1, 2, 3]
def baseStart_4775290 : Nat := 118140960795 + 4775290 * 2 ^ 59
def prefixEnd_4775290 : Nat := 4983230072969 + 3 ^ 40 * 4775290 * 2
def baseEnd_4775290 : Nat := 2452019034608726889613847

theorem tailTrace_4775290 : CollatzResearch.WordTrace tailWord_4775290 prefixEnd_4775290 2452019034608726889613847 := by
  unfold tailWord_4775290
  simp only [CollatzResearch.WordTrace]
  refine ⟨43542283717486839861872831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116112756579964906298327549 43542283717486839861872831)
  ·
    refine ⟨65313425576230259792809247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43542283717486839861872831 65313425576230259792809247)
    ·
      refine ⟨97970138364345389689213871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65313425576230259792809247 97970138364345389689213871)
      ·
        refine ⟨146955207546518084533820807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97970138364345389689213871 146955207546518084533820807)
        ·
          refine ⟨220432811319777126800731211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146955207546518084533820807 220432811319777126800731211)
          ·
            refine ⟨330649216979665690201096817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220432811319777126800731211 330649216979665690201096817)
            ·
              refine ⟨247986912734749267650822613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 330649216979665690201096817 247986912734749267650822613)
              ·
                refine ⟨5812193267220685960566155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 247986912734749267650822613 5812193267220685960566155)
                ·
                  refine ⟨8718289900831028940849233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5812193267220685960566155 8718289900831028940849233)
                  ·
                    refine ⟨6538717425623271705636925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8718289900831028940849233 6538717425623271705636925)
                    ·
                      refine ⟨2452019034608726889613847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6538717425623271705636925 2452019034608726889613847)
                      ·
                        rfl

theorem cell23_4775290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 7, 1, 2, 3].length) (baseStart_4775290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775290 prefixEnd_4775290 := by exact prefixLift 4775290
  have htrace : WordTrace (prefixWord ++ tailWord_4775290) baseStart_4775290 baseEnd_4775290 := by
    simpa [prefixWord, tailWord_4775290, baseEnd_4775290] using wordTrace_append hprefix tailTrace_4775290
  have hstable : (prefixWord ++ tailWord_4775290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775290).length < 2 ^ (prefixWord ++ tailWord_4775290).sum := by decide
  have hdescent : baseEnd_4775290 < baseStart_4775290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775297 : List Nat := [1, 2, 4, 3, 2, 1, 1, 1, 4, 4]
def baseStart_4775297 : Nat := 118140960795 + 4775297 * 2 ^ 59
def prefixEnd_4775297 : Nat := 4983230072969 + 3 ^ 40 * 4775297 * 2
def baseEnd_4775297 : Nat := 817340876324436120742105

theorem tailTrace_4775297 : CollatzResearch.WordTrace tailWord_4775297 prefixEnd_4775297 817340876324436120742105 := by
  unfold tailWord_4775297
  simp only [CollatzResearch.WordTrace]
  refine ⟨174169390180921999642996145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116112926787281333095330763 174169390180921999642996145)
  ·
    refine ⟨130627042635691499732247109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174169390180921999642996145 130627042635691499732247109)
    ·
      refine ⟨24492570494192156199796333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130627042635691499732247109 24492570494192156199796333)
      ·
        refine ⟨9184713935322058574923625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24492570494192156199796333 9184713935322058574923625)
        ·
          refine ⟨6888535451491543931192719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9184713935322058574923625 6888535451491543931192719)
          ·
            refine ⟨10332803177237315896789079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6888535451491543931192719 10332803177237315896789079)
            ·
              refine ⟨15499204765855973845183619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10332803177237315896789079 15499204765855973845183619)
              ·
                refine ⟨23248807148783960767775429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15499204765855973845183619 23248807148783960767775429)
                ·
                  refine ⟨4359151340396992643957893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23248807148783960767775429 4359151340396992643957893)
                  ·
                    refine ⟨817340876324436120742105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4359151340396992643957893 817340876324436120742105)
                    ·
                      rfl

theorem cell23_4775297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_4775297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775297 prefixEnd_4775297 := by exact prefixLift 4775297
  have htrace : WordTrace (prefixWord ++ tailWord_4775297) baseStart_4775297 baseEnd_4775297 := by
    simpa [prefixWord, tailWord_4775297, baseEnd_4775297] using wordTrace_append hprefix tailTrace_4775297
  have hstable : (prefixWord ++ tailWord_4775297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775297).length < 2 ^ (prefixWord ++ tailWord_4775297).sum := by decide
  have hdescent : baseEnd_4775297 < baseStart_4775297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775304 : List Nat := [2, 1, 3, 3, 1, 3, 2, 1, 3, 2, 2]
def baseStart_4775304 : Nat := 118140960795 + 4775304 * 2 ^ 59
def prefixEnd_4775304 : Nat := 4983230072969 + 3 ^ 40 * 4775304 * 2
def baseEnd_4775304 : Nat := 2452026223337889834838783

theorem tailTrace_4775304 : CollatzResearch.WordTrace tailWord_4775304 prefixEnd_4775304 2452026223337889834838783 := by
  unfold tailWord_4775304
  simp only [CollatzResearch.WordTrace]
  refine ⟨87084822745948319919250483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116113096994597759892333977 87084822745948319919250483)
  ·
    refine ⟨130627234118922479878875725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87084822745948319919250483 130627234118922479878875725)
    ·
      refine ⟨48985212794595929954578397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130627234118922479878875725 48985212794595929954578397)
      ·
        refine ⟨18369454797973473732966899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48985212794595929954578397 18369454797973473732966899)
        ·
          refine ⟨27554182196960210599450349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18369454797973473732966899 27554182196960210599450349)
          ·
            refine ⟨10332818323860078974793881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27554182196960210599450349 10332818323860078974793881)
            ·
              refine ⟨7749613742895059231095411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10332818323860078974793881 7749613742895059231095411)
              ·
                refine ⟨11624420614342588846643117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7749613742895059231095411 11624420614342588846643117)
                ·
                  refine ⟨4359157730378470817491169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11624420614342588846643117 4359157730378470817491169)
                  ·
                    refine ⟨3269368297783853113118377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4359157730378470817491169 3269368297783853113118377)
                    ·
                      refine ⟨2452026223337889834838783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3269368297783853113118377 2452026223337889834838783)
                      ·
                        rfl

theorem cell23_4775304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_4775304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775304 prefixEnd_4775304 := by exact prefixLift 4775304
  have htrace : WordTrace (prefixWord ++ tailWord_4775304) baseStart_4775304 baseEnd_4775304 := by
    simpa [prefixWord, tailWord_4775304, baseEnd_4775304] using wordTrace_append hprefix tailTrace_4775304
  have hstable : (prefixWord ++ tailWord_4775304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775304).length < 2 ^ (prefixWord ++ tailWord_4775304).sum := by decide
  have hdescent : baseEnd_4775304 < baseStart_4775304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775314 : List Nat := [3, 2, 3, 3, 1, 2, 1, 1, 1, 6]
def baseStart_4775314 : Nat := 118140960795 + 4775314 * 2 ^ 59
def prefixEnd_4775314 : Nat := 4983230072969 + 3 ^ 40 * 4775314 * 2
def baseEnd_4775314 : Nat := 817343786048144931904579

theorem tailTrace_4775314 : CollatzResearch.WordTrace tailWord_4775314 prefixEnd_4775314 817343786048144931904579 := by
  unfold tailWord_4775314
  simp only [CollatzResearch.WordTrace]
  refine ⟨43542502555465102886591249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116113340147906941030909997 43542502555465102886591249)
  ·
    refine ⟨32656876916598827164943437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43542502555465102886591249 32656876916598827164943437)
    ·
      refine ⟨12246328843724560186853789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32656876916598827164943437 12246328843724560186853789)
      ·
        refine ⟨4592373316396710070070171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12246328843724560186853789 4592373316396710070070171)
        ·
          refine ⟨6888559974595065105105257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4592373316396710070070171 6888559974595065105105257)
          ·
            refine ⟨5166419980946298828828943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6888559974595065105105257 5166419980946298828828943)
            ·
              refine ⟨7749629971419448243243415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5166419980946298828828943 7749629971419448243243415)
              ·
                refine ⟨11624444957129172364865123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7749629971419448243243415 11624444957129172364865123)
                ·
                  refine ⟨17436667435693758547297685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11624444957129172364865123 17436667435693758547297685)
                  ·
                    refine ⟨817343786048144931904579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17436667435693758547297685 817343786048144931904579)
                    ·
                      rfl

theorem cell23_4775314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_4775314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775314 prefixEnd_4775314 := by exact prefixLift 4775314
  have htrace : WordTrace (prefixWord ++ tailWord_4775314) baseStart_4775314 baseEnd_4775314 := by
    simpa [prefixWord, tailWord_4775314, baseEnd_4775314] using wordTrace_append hprefix tailTrace_4775314
  have hstable : (prefixWord ++ tailWord_4775314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775314).length < 2 ^ (prefixWord ++ tailWord_4775314).sum := by decide
  have hdescent : baseEnd_4775314 < baseStart_4775314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775383 : List Nat := [1, 1, 3, 2, 1, 1, 1, 6, 7]
def baseStart_4775383 : Nat := 118140960795 + 4775383 * 2 ^ 59
def prefixEnd_4775383 : Nat := 4983230072969 + 3 ^ 40 * 4775383 * 2
def baseEnd_4775383 : Nat := 272451865367732780638991

theorem tailTrace_4775383 : CollatzResearch.WordTrace tailWord_4775383 prefixEnd_4775383 272451865367732780638991 := by
  unfold tailWord_4775383
  simp only [CollatzResearch.WordTrace]
  refine ⟨174172526858610436330626803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116115017905740290887084535 174172526858610436330626803)
  ·
    refine ⟨261258790287915654495940205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174172526858610436330626803 261258790287915654495940205)
    ·
      refine ⟨97972046357968370435977577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 261258790287915654495940205 97972046357968370435977577)
      ·
        refine ⟨73479034768476277826983183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97972046357968370435977577 73479034768476277826983183)
        ·
          refine ⟨110218552152714416740474775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73479034768476277826983183 110218552152714416740474775)
          ·
            refine ⟨165327828229071625110712163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110218552152714416740474775 165327828229071625110712163)
            ·
              refine ⟨247991742343607437666068245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165327828229071625110712163 247991742343607437666068245)
              ·
                refine ⟨11624612922356598640596949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 247991742343607437666068245 11624612922356598640596949)
                ·
                  refine ⟨272451865367732780638991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11624612922356598640596949 272451865367732780638991)
                  ·
                    rfl

theorem cell23_4775383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 7].length) (baseStart_4775383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775383 prefixEnd_4775383 := by exact prefixLift 4775383
  have htrace : WordTrace (prefixWord ++ tailWord_4775383) baseStart_4775383 baseEnd_4775383 := by
    simpa [prefixWord, tailWord_4775383, baseEnd_4775383] using wordTrace_append hprefix tailTrace_4775383
  have hstable : (prefixWord ++ tailWord_4775383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775383).length < 2 ^ (prefixWord ++ tailWord_4775383).sum := by decide
  have hdescent : baseEnd_4775383 < baseStart_4775383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775423 : List Nat := [1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 7]
def baseStart_4775423 : Nat := 118140960795 + 4775423 * 2 ^ 59
def prefixEnd_4775423 : Nat := 4983230072969 + 3 ^ 40 * 4775423 * 2
def baseEnd_4775423 : Nat := 2452087327535774869250735

theorem tailTrace_4775423 : CollatzResearch.WordTrace tailWord_4775423 prefixEnd_4775423 2452087327535774869250735 := by
  unfold tailWord_4775423
  simp only [CollatzResearch.WordTrace]
  refine ⟨174173985778465523162082923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116115990518977015441388615 174173985778465523162082923)
  ·
    refine ⟨261260978667698284743124385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174173985778465523162082923 261260978667698284743124385)
    ·
      refine ⟨195945734000773713557343289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261260978667698284743124385 195945734000773713557343289)
      ·
        refine ⟨146959300500580285168007467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195945734000773713557343289 146959300500580285168007467)
        ·
          refine ⟨220438950750870427752011201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146959300500580285168007467 220438950750870427752011201)
          ·
            refine ⟨165329213063152820814008401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220438950750870427752011201 165329213063152820814008401)
            ·
              refine ⟨123996909797364615610506301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165329213063152820814008401 123996909797364615610506301)
              ·
                refine ⟨46498841174011730853939863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123996909797364615610506301 46498841174011730853939863)
                ·
                  refine ⟨69748261761017596280909795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46498841174011730853939863 69748261761017596280909795)
                  ·
                    refine ⟨104622392641526394421364693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69748261761017596280909795 104622392641526394421364693)
                    ·
                      refine ⟨2452087327535774869250735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 104622392641526394421364693 2452087327535774869250735)
                      ·
                        rfl

theorem cell23_4775423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_4775423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775423 prefixEnd_4775423 := by exact prefixLift 4775423
  have htrace : WordTrace (prefixWord ++ tailWord_4775423) baseStart_4775423 baseEnd_4775423 := by
    simpa [prefixWord, tailWord_4775423, baseEnd_4775423] using wordTrace_append hprefix tailTrace_4775423
  have hstable : (prefixWord ++ tailWord_4775423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775423).length < 2 ^ (prefixWord ++ tailWord_4775423).sum := by decide
  have hdescent : baseEnd_4775423 < baseStart_4775423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775477 : List Nat := [1, 3, 3, 1, 1, 3, 1, 3, 3, 4]
def baseStart_4775477 : Nat := 118140960795 + 4775477 * 2 ^ 59
def prefixEnd_4775477 : Nat := 4983230072969 + 3 ^ 40 * 4775477 * 2
def baseEnd_4775477 : Nat := 817371685163705885991829

theorem tailTrace_4775477 : CollatzResearch.WordTrace tailWord_4775477 prefixEnd_4775477 817371685163705885991829 := by
  unfold tailWord_4775477
  simp only [CollatzResearch.WordTrace]
  refine ⟨174175955320269890384548685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116117303546846593589699123 174175955320269890384548685)
  ·
    refine ⟨65315983245101208894205757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174175955320269890384548685 65315983245101208894205757)
    ·
      refine ⟨24493493716912953335327159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65315983245101208894205757 24493493716912953335327159)
      ·
        refine ⟨36740240575369430002990739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24493493716912953335327159 36740240575369430002990739)
        ·
          refine ⟨55110360863054145004486109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36740240575369430002990739 55110360863054145004486109)
          ·
            refine ⟨20666385323645304376682291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55110360863054145004486109 20666385323645304376682291)
            ·
              refine ⟨30999577985467956565023437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20666385323645304376682291 30999577985467956565023437)
              ·
                refine ⟨11624841744550483711883789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30999577985467956565023437 11624841744550483711883789)
                ·
                  refine ⟨4359315654206431391956421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11624841744550483711883789 4359315654206431391956421)
                  ·
                    refine ⟨817371685163705885991829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4359315654206431391956421 817371685163705885991829)
                    ·
                      rfl

theorem cell23_4775477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_4775477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775477 prefixEnd_4775477 := by exact prefixLift 4775477
  have htrace : WordTrace (prefixWord ++ tailWord_4775477) baseStart_4775477 baseEnd_4775477 := by
    simpa [prefixWord, tailWord_4775477, baseEnd_4775477] using wordTrace_append hprefix tailTrace_4775477
  have hstable : (prefixWord ++ tailWord_4775477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775477).length < 2 ^ (prefixWord ++ tailWord_4775477).sum := by decide
  have hdescent : baseEnd_4775477 < baseStart_4775477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775511 : List Nat := [1, 1, 3, 2, 2, 5, 1, 3, 1, 4]
def baseStart_4775511 : Nat := 118140960795 + 4775511 * 2 ^ 59
def prefixEnd_4775511 : Nat := 4983230072969 + 3 ^ 40 * 4775511 * 2
def baseEnd_4775511 : Nat := 817377504611123508316777

theorem tailTrace_4775511 : CollatzResearch.WordTrace tailWord_4775511 prefixEnd_4775511 817377504611123508316777 := by
  unfold tailWord_4775511
  simp only [CollatzResearch.WordTrace]
  refine ⟨174177195402146714191286387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116118130268097809460857591 174177195402146714191286387)
  ·
    refine ⟨261265793103220071286929581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174177195402146714191286387 261265793103220071286929581)
    ·
      refine ⟨97974672413707526732598593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 261265793103220071286929581 97974672413707526732598593)
      ·
        refine ⟨73481004310280645049448945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97974672413707526732598593 73481004310280645049448945)
        ·
          refine ⟨55110753232710483787086709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73481004310280645049448945 55110753232710483787086709)
          ·
            refine ⟨5166633115566607855039379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55110753232710483787086709 5166633115566607855039379)
            ·
              refine ⟨7749949673349911782559069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5166633115566607855039379 7749949673349911782559069)
              ·
                refine ⟨2906231127506216918459651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7749949673349911782559069 2906231127506216918459651)
                ·
                  refine ⟨4359346691259325377689477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2906231127506216918459651 4359346691259325377689477)
                  ·
                    refine ⟨817377504611123508316777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4359346691259325377689477 817377504611123508316777)
                    ·
                      rfl

theorem cell23_4775511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 3, 1, 4].length) (baseStart_4775511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775511 prefixEnd_4775511 := by exact prefixLift 4775511
  have htrace : WordTrace (prefixWord ++ tailWord_4775511) baseStart_4775511 baseEnd_4775511 := by
    simpa [prefixWord, tailWord_4775511, baseEnd_4775511] using wordTrace_append hprefix tailTrace_4775511
  have hstable : (prefixWord ++ tailWord_4775511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775511).length < 2 ^ (prefixWord ++ tailWord_4775511).sum := by decide
  have hdescent : baseEnd_4775511 < baseStart_4775511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775520 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 5, 5]
def baseStart_4775520 : Nat := 118140960795 + 4775520 * 2 ^ 59
def prefixEnd_4775520 : Nat := 4983230072969 + 3 ^ 40 * 4775520 * 2
def baseEnd_4775520 : Nat := 817379045053086996579263

theorem tailTrace_4775520 : CollatzResearch.WordTrace tailWord_4775520 prefixEnd_4775520 817379045053086996579263 := by
  unfold tailWord_4775520
  simp only [CollatzResearch.WordTrace]
  refine ⟨87088761829557054364182007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116118349106076072485576009 87088761829557054364182007)
  ·
    refine ⟨130633142744335581546273011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87088761829557054364182007 130633142744335581546273011)
    ·
      refine ⟨195949714116503372319409517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130633142744335581546273011 195949714116503372319409517)
      ·
        refine ⟨73481142793688764619778569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195949714116503372319409517 73481142793688764619778569)
        ·
          refine ⟨55110857095266573464833927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73481142793688764619778569 55110857095266573464833927)
          ·
            refine ⟨82666285642899860197250891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55110857095266573464833927 82666285642899860197250891)
            ·
              refine ⟨123999428464349790295876337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82666285642899860197250891 123999428464349790295876337)
              ·
                refine ⟨92999571348262342721907253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123999428464349790295876337 92999571348262342721907253)
                ·
                  refine ⟨8718709813899594630178805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 92999571348262342721907253 8718709813899594630178805)
                  ·
                    refine ⟨817379045053086996579263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8718709813899594630178805 817379045053086996579263)
                    ·
                      rfl

theorem cell23_4775520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 5, 5].length) (baseStart_4775520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775520 prefixEnd_4775520 := by exact prefixLift 4775520
  have htrace : WordTrace (prefixWord ++ tailWord_4775520) baseStart_4775520 baseEnd_4775520 := by
    simpa [prefixWord, tailWord_4775520, baseEnd_4775520] using wordTrace_append hprefix tailTrace_4775520
  have hstable : (prefixWord ++ tailWord_4775520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775520).length < 2 ^ (prefixWord ++ tailWord_4775520).sum := by decide
  have hdescent : baseEnd_4775520 < baseStart_4775520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775528 : List Nat := [2, 1, 4, 3, 1, 2, 3, 2, 1, 4]
def baseStart_4775528 : Nat := 118140960795 + 4775528 * 2 ^ 59
def prefixEnd_4775528 : Nat := 4983230072969 + 3 ^ 40 * 4775528 * 2
def baseEnd_4775528 : Nat := 817380414334832319479251

theorem tailTrace_4775528 : CollatzResearch.WordTrace tailWord_4775528 prefixEnd_4775528 817380414334832319479251 := by
  unfold tailWord_4775528
  simp only [CollatzResearch.WordTrace]
  refine ⟨87088907721542563047327619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116118543628723417396436825 87088907721542563047327619)
  ·
    refine ⟨130633361582313844570991429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87088907721542563047327619 130633361582313844570991429)
    ·
      refine ⟨24493755296683845857060893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130633361582313844570991429 24493755296683845857060893)
      ·
        refine ⟨9185158236256442196397835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24493755296683845857060893 9185158236256442196397835)
        ·
          refine ⟨13777737354384663294596753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9185158236256442196397835 13777737354384663294596753)
          ·
            refine ⟨10333303015788497470947565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13777737354384663294596753 10333303015788497470947565)
            ·
              refine ⟨3874988630920686551605337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10333303015788497470947565 3874988630920686551605337)
              ·
                refine ⟨2906241473190514913704003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3874988630920686551605337 2906241473190514913704003)
                ·
                  refine ⟨4359362209785772370556005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2906241473190514913704003 4359362209785772370556005)
                  ·
                    refine ⟨817380414334832319479251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4359362209785772370556005 817380414334832319479251)
                    ·
                      rfl

theorem cell23_4775528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_4775528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775528 prefixEnd_4775528 := by exact prefixLift 4775528
  have htrace : WordTrace (prefixWord ++ tailWord_4775528) baseStart_4775528 baseEnd_4775528 := by
    simpa [prefixWord, tailWord_4775528, baseEnd_4775528] using wordTrace_append hprefix tailTrace_4775528
  have hstable : (prefixWord ++ tailWord_4775528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775528).length < 2 ^ (prefixWord ++ tailWord_4775528).sum := by decide
  have hdescent : baseEnd_4775528 < baseStart_4775528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775541 : List Nat := [1, 3, 4, 2, 1, 3, 2, 1, 6]
def baseStart_4775541 : Nat := 118140960795 + 4775541 * 2 ^ 59
def prefixEnd_4775541 : Nat := 4983230072969 + 3 ^ 40 * 4775541 * 2
def baseEnd_4775541 : Nat := 272460879805889489730577

theorem tailTrace_4775541 : CollatzResearch.WordTrace tailWord_4775541 prefixEnd_4775541 272460879805889489730577 := by
  unfold tailWord_4775541
  simp only [CollatzResearch.WordTrace]
  refine ⟨174178289592038029314878477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116118859728025352876585651 174178289592038029314878477)
  ·
    refine ⟨65316858597014260993079429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174178289592038029314878477 65316858597014260993079429)
    ·
      refine ⟨12246910986940173936202393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65316858597014260993079429 12246910986940173936202393)
      ·
        refine ⟨9185183240205130452151795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12246910986940173936202393 9185183240205130452151795)
        ·
          refine ⟨13777774860307695678227693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9185183240205130452151795 13777774860307695678227693)
          ·
            refine ⟨5166665572615385879335385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13777774860307695678227693 5166665572615385879335385)
            ·
              refine ⟨3874999179461539409501539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5166665572615385879335385 3874999179461539409501539)
              ·
                refine ⟨5812498769192309114252309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3874999179461539409501539 5812498769192309114252309)
                ·
                  refine ⟨272460879805889489730577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5812498769192309114252309 272460879805889489730577)
                  ·
                    rfl

theorem cell23_4775541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 1, 6].length) (baseStart_4775541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775541 prefixEnd_4775541 := by exact prefixLift 4775541
  have htrace : WordTrace (prefixWord ++ tailWord_4775541) baseStart_4775541 baseEnd_4775541 := by
    simpa [prefixWord, tailWord_4775541, baseEnd_4775541] using wordTrace_append hprefix tailTrace_4775541
  have hstable : (prefixWord ++ tailWord_4775541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775541).length < 2 ^ (prefixWord ++ tailWord_4775541).sum := by decide
  have hdescent : baseEnd_4775541 < baseStart_4775541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775557 : List Nat := [1, 3, 1, 1, 4, 1, 3, 1, 3, 1, 4]
def baseStart_4775557 : Nat := 118140960795 + 4775557 * 2 ^ 59
def prefixEnd_4775557 : Nat := 4983230072969 + 3 ^ 40 * 4775557 * 2
def baseEnd_4775557 : Nat := 2452156133943477344975119

theorem tailTrace_4775557 : CollatzResearch.WordTrace tailWord_4775557 prefixEnd_4775557 2452156133943477344975119 := by
  unfold tailWord_4775557
  simp only [CollatzResearch.WordTrace]
  refine ⟨174178873159980064047460925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116119248773320042698307283 174178873159980064047460925)
  ·
    refine ⟨65317077434992524017797847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174178873159980064047460925 65317077434992524017797847)
    ·
      refine ⟨97975616152488786026696771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65317077434992524017797847 97975616152488786026696771)
      ·
        refine ⟨146963424228733179040045157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97975616152488786026696771 146963424228733179040045157)
        ·
          refine ⟨27555642042887471070008467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 146963424228733179040045157 27555642042887471070008467)
          ·
            refine ⟨41333463064331206605012701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27555642042887471070008467 41333463064331206605012701)
            ·
              refine ⟨15500048649124202476879763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41333463064331206605012701 15500048649124202476879763)
              ·
                refine ⟨23250072973686303715319645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15500048649124202476879763 23250072973686303715319645)
                ·
                  refine ⟨8718777365132363893244867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23250072973686303715319645 8718777365132363893244867)
                  ·
                    refine ⟨13078166047698545839867301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8718777365132363893244867 13078166047698545839867301)
                    ·
                      refine ⟨2452156133943477344975119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13078166047698545839867301 2452156133943477344975119)
                      ·
                        rfl

theorem cell23_4775557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 3, 1, 4].length) (baseStart_4775557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775557 prefixEnd_4775557 := by exact prefixLift 4775557
  have htrace : WordTrace (prefixWord ++ tailWord_4775557) baseStart_4775557 baseEnd_4775557 := by
    simpa [prefixWord, tailWord_4775557, baseEnd_4775557] using wordTrace_append hprefix tailTrace_4775557
  have hstable : (prefixWord ++ tailWord_4775557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775557).length < 2 ^ (prefixWord ++ tailWord_4775557).sum := by decide
  have hdescent : baseEnd_4775557 < baseStart_4775557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775580 : List Nat := [2, 2, 3, 2, 14]
def baseStart_4775580 : Nat := 118140960795 + 4775580 * 2 ^ 59
def prefixEnd_4775580 : Nat := 4983230072969 + 3 ^ 40 * 4775580 * 2
def baseEnd_4775580 : Nat := 3363742035663279499297

theorem tailTrace_4775580 : CollatzResearch.WordTrace tailWord_4775580 prefixEnd_4775580 3363742035663279499297 := by
  unfold tailWord_4775580
  simp only [CollatzResearch.WordTrace]
  refine ⟨87089856019448369487774097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116119808025931159317032129 87089856019448369487774097)
  ·
    refine ⟨65317392014586277115830573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87089856019448369487774097 65317392014586277115830573)
    ·
      refine ⟨24494022005469853918436465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65317392014586277115830573 24494022005469853918436465)
      ·
        refine ⟨18370516504102390438827349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24494022005469853918436465 18370516504102390438827349)
        ·
          refine ⟨3363742035663279499297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 18370516504102390438827349 3363742035663279499297)
          ·
            rfl

theorem cell23_4775580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 14].length) (baseStart_4775580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775580 prefixEnd_4775580 := by exact prefixLift 4775580
  have htrace : WordTrace (prefixWord ++ tailWord_4775580) baseStart_4775580 baseEnd_4775580 := by
    simpa [prefixWord, tailWord_4775580, baseEnd_4775580] using wordTrace_append hprefix tailTrace_4775580
  have hstable : (prefixWord ++ tailWord_4775580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775580).length < 2 ^ (prefixWord ++ tailWord_4775580).sum := by decide
  have hdescent : baseEnd_4775580 < baseStart_4775580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775584 : List Nat := [2, 1, 1, 4, 3, 1, 1, 4, 2, 4]
def baseStart_4775584 : Nat := 118140960795 + 4775584 * 2 ^ 59
def prefixEnd_4775584 : Nat := 4983230072969 + 3 ^ 40 * 4775584 * 2
def baseEnd_4775584 : Nat := 817389999307049579779165

theorem tailTrace_4775584 : CollatzResearch.WordTrace tailWord_4775584 prefixEnd_4775584 817389999307049579779165 := by
  unfold tailWord_4775584
  simp only [CollatzResearch.WordTrace]
  refine ⟨87089928965441123829346903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116119905287254831772462537 87089928965441123829346903)
  ·
    refine ⟨130634893448161685744020355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87089928965441123829346903 130634893448161685744020355)
    ·
      refine ⟨195952340172242528616030533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130634893448161685744020355 195952340172242528616030533)
      ·
        refine ⟨36741063782295474115505725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 195952340172242528616030533 36741063782295474115505725)
        ·
          refine ⟨13777898918360802793314647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36741063782295474115505725 13777898918360802793314647)
          ·
            refine ⟨20666848377541204189971971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13777898918360802793314647 20666848377541204189971971)
            ·
              refine ⟨31000272566311806284957957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20666848377541204189971971 31000272566311806284957957)
              ·
                refine ⟨5812551106183463678429617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31000272566311806284957957 5812551106183463678429617)
                ·
                  refine ⟨4359413329637597758822213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5812551106183463678429617 4359413329637597758822213)
                  ·
                    refine ⟨817389999307049579779165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4359413329637597758822213 817389999307049579779165)
                    ·
                      rfl

theorem cell23_4775584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4, 2, 4].length) (baseStart_4775584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775584 prefixEnd_4775584 := by exact prefixLift 4775584
  have htrace : WordTrace (prefixWord ++ tailWord_4775584) baseStart_4775584 baseEnd_4775584 := by
    simpa [prefixWord, tailWord_4775584, baseEnd_4775584] using wordTrace_append hprefix tailTrace_4775584
  have hstable : (prefixWord ++ tailWord_4775584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775584).length < 2 ^ (prefixWord ++ tailWord_4775584).sum := by decide
  have hdescent : baseEnd_4775584 < baseStart_4775584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775585 : List Nat := [1, 2, 3, 3, 2, 3, 2, 2, 1, 1, 3]
def baseStart_4775585 : Nat := 118140960795 + 4775585 * 2 ^ 59
def prefixEnd_4775585 : Nat := 4983230072969 + 3 ^ 40 * 4775585 * 2
def baseEnd_4775585 : Nat := 2452170511401803235424991

theorem tailTrace_4775585 : CollatzResearch.WordTrace tailWord_4775585 prefixEnd_4775585 2452170511401803235424991 := by
  unfold tailWord_4775585
  simp only [CollatzResearch.WordTrace]
  refine ⟨174179894403878624829480209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116119929602585749886320139 174179894403878624829480209)
  ·
    refine ⟨130634920802908968622110157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174179894403878624829480209 130634920802908968622110157)
    ·
      refine ⟨48988095301090863233291309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130634920802908968622110157 48988095301090863233291309)
      ·
        refine ⟨18370535737909073712484241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48988095301090863233291309 18370535737909073712484241)
        ·
          refine ⟨13777901803431805284363181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18370535737909073712484241 13777901803431805284363181)
          ·
            refine ⟨5166713176286926981636193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13777901803431805284363181 5166713176286926981636193)
            ·
              refine ⟨3875034882215195236227145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5166713176286926981636193 3875034882215195236227145)
              ·
                refine ⟨2906276161661396427170359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3875034882215195236227145 2906276161661396427170359)
                ·
                  refine ⟨4359414242492094640755539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2906276161661396427170359 4359414242492094640755539)
                  ·
                    refine ⟨6539121363738141961133309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4359414242492094640755539 6539121363738141961133309)
                    ·
                      refine ⟨2452170511401803235424991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6539121363738141961133309 2452170511401803235424991)
                      ·
                        rfl

theorem cell23_4775585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_4775585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775585 prefixEnd_4775585 := by exact prefixLift 4775585
  have htrace : WordTrace (prefixWord ++ tailWord_4775585) baseStart_4775585 baseEnd_4775585 := by
    simpa [prefixWord, tailWord_4775585, baseEnd_4775585] using wordTrace_append hprefix tailTrace_4775585
  have hstable : (prefixWord ++ tailWord_4775585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775585).length < 2 ^ (prefixWord ++ tailWord_4775585).sum := by decide
  have hdescent : baseEnd_4775585 < baseStart_4775585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775600 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 6]
def baseStart_4775600 : Nat := 118140960795 + 4775600 * 2 ^ 59
def prefixEnd_4775600 : Nat := 4983230072969 + 3 ^ 40 * 4775600 * 2
def baseEnd_4775600 : Nat := 2452178213611620676737421

theorem tailTrace_4775600 : CollatzResearch.WordTrace tailWord_4775600 prefixEnd_4775600 2452178213611620676737421 := by
  unfold tailWord_4775600
  simp only [CollatzResearch.WordTrace]
  refine ⟨87090220749412141195638127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116120294332549521594184169 87090220749412141195638127)
  ·
    refine ⟨130635331124118211793457191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87090220749412141195638127 130635331124118211793457191)
    ·
      refine ⟨195952996686177317690185787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130635331124118211793457191 195952996686177317690185787)
      ·
        refine ⟨293929495029265976535278681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195952996686177317690185787 293929495029265976535278681)
        ·
          refine ⟨220447121271949482401459011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 293929495029265976535278681 220447121271949482401459011)
          ·
            refine ⟨330670681907924223602188517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220447121271949482401459011 330670681907924223602188517)
            ·
              refine ⟨62000752857735791925410347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 330670681907924223602188517 62000752857735791925410347)
              ·
                refine ⟨93001129286603687888115521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62000752857735791925410347 93001129286603687888115521)
                ·
                  refine ⟨69750846964952765916086641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93001129286603687888115521 69750846964952765916086641)
                  ·
                    refine ⟨52313135223714574437064981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 69750846964952765916086641 52313135223714574437064981)
                    ·
                      refine ⟨2452178213611620676737421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52313135223714574437064981 2452178213611620676737421)
                      ·
                        rfl

theorem cell23_4775600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 6].length) (baseStart_4775600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775600 prefixEnd_4775600 := by exact prefixLift 4775600
  have htrace : WordTrace (prefixWord ++ tailWord_4775600) baseStart_4775600 baseEnd_4775600 := by
    simpa [prefixWord, tailWord_4775600, baseEnd_4775600] using wordTrace_append hprefix tailTrace_4775600
  have hstable : (prefixWord ++ tailWord_4775600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775600).length < 2 ^ (prefixWord ++ tailWord_4775600).sum := by decide
  have hdescent : baseEnd_4775600 < baseStart_4775600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775614 : List Nat := [4, 2, 1, 1, 2, 3, 3, 7]
def baseStart_4775614 : Nat := 118140960795 + 4775614 * 2 ^ 59
def prefixEnd_4775614 : Nat := 4983230072969 + 3 ^ 40 * 4775614 * 2
def baseEnd_4775614 : Nat := 90821681568177171183791

theorem tailTrace_4775614 : CollatzResearch.WordTrace tailWord_4775614 prefixEnd_4775614 90821681568177171183791 := by
  unfold tailWord_4775614
  simp only [CollatzResearch.WordTrace]
  refine ⟨21772619015096695347785737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116120634747182375188190597 21772619015096695347785737)
  ·
    refine ⟨16329464261322521510839303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21772619015096695347785737 16329464261322521510839303)
    ·
      refine ⟨24494196391983782266258955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16329464261322521510839303 24494196391983782266258955)
      ·
        refine ⟨36741294587975673399388433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24494196391983782266258955 36741294587975673399388433)
        ·
          refine ⟨27555970940981755049541325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36741294587975673399388433 27555970940981755049541325)
          ·
            refine ⟨10333489102868158143577997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27555970940981755049541325 10333489102868158143577997)
            ·
              refine ⟨3875058413575559303841749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10333489102868158143577997 3875058413575559303841749)
              ·
                refine ⟨90821681568177171183791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3875058413575559303841749 90821681568177171183791)
                ·
                  rfl

theorem cell23_4775614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 7].length) (baseStart_4775614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775614 prefixEnd_4775614 := by exact prefixLift 4775614
  have htrace : WordTrace (prefixWord ++ tailWord_4775614) baseStart_4775614 baseEnd_4775614 := by
    simpa [prefixWord, tailWord_4775614, baseEnd_4775614] using wordTrace_append hprefix tailTrace_4775614
  have hstable : (prefixWord ++ tailWord_4775614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775614).length < 2 ^ (prefixWord ++ tailWord_4775614).sum := by decide
  have hdescent : baseEnd_4775614 < baseStart_4775614 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775624 : List Nat := [2, 1, 3, 1, 2, 2, 2, 2, 4, 1, 3]
def baseStart_4775624 : Nat := 118140960795 + 4775624 * 2 ^ 59
def prefixEnd_4775624 : Nat := 4983230072969 + 3 ^ 40 * 4775624 * 2
def baseEnd_4775624 : Nat := 2452190537147328582837311

theorem tailTrace_4775624 : CollatzResearch.WordTrace tailWord_4775624 prefixEnd_4775624 2452190537147328582837311 := by
  unfold tailWord_4775624
  simp only [CollatzResearch.WordTrace]
  refine ⟨87090658425368667245074963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116120877900491556326766617 87090658425368667245074963)
  ·
    refine ⟨130635987638053000867612445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87090658425368667245074963 130635987638053000867612445)
    ·
      refine ⟨48988495364269875325354667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130635987638053000867612445 48988495364269875325354667)
      ·
        refine ⟨73482743046404812988032001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48988495364269875325354667 73482743046404812988032001)
        ·
          refine ⟨55112057284803609741024001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73482743046404812988032001 55112057284803609741024001)
          ·
            refine ⟨41334042963602707305768001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55112057284803609741024001 41334042963602707305768001)
            ·
              refine ⟨31000532222702030479326001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41334042963602707305768001 31000532222702030479326001)
              ·
                refine ⟨23250399167026522859494501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31000532222702030479326001 23250399167026522859494501)
                ·
                  refine ⟨4359449843817473036155219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23250399167026522859494501 4359449843817473036155219)
                  ·
                    refine ⟨6539174765726209554232829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4359449843817473036155219 6539174765726209554232829)
                    ·
                      refine ⟨2452190537147328582837311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6539174765726209554232829 2452190537147328582837311)
                      ·
                        rfl

theorem cell23_4775624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 4, 1, 3].length) (baseStart_4775624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775624 prefixEnd_4775624 := by exact prefixLift 4775624
  have htrace : WordTrace (prefixWord ++ tailWord_4775624) baseStart_4775624 baseEnd_4775624 := by
    simpa [prefixWord, tailWord_4775624, baseEnd_4775624] using wordTrace_append hprefix tailTrace_4775624
  have hstable : (prefixWord ++ tailWord_4775624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775624).length < 2 ^ (prefixWord ++ tailWord_4775624).sum := by decide
  have hdescent : baseEnd_4775624 < baseStart_4775624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775641 : List Nat := [1, 2, 1, 2, 3, 3, 3, 2, 2, 1, 3]
def baseStart_4775641 : Nat := 118140960795 + 4775641 * 2 ^ 59
def prefixEnd_4775641 : Nat := 4983230072969 + 3 ^ 40 * 4775641 * 2
def baseEnd_4775641 : Nat := 2452199266318455016324733

theorem tailTrace_4775641 : CollatzResearch.WordTrace tailWord_4775641 prefixEnd_4775641 2452199266318455016324733 := by
  unfold tailWord_4775641
  simp only [CollatzResearch.WordTrace]
  refine ⟨174181936891675746393518777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116121291261117164262345851 174181936891675746393518777)
  ·
    refine ⟨130636452668756809795139083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174181936891675746393518777 130636452668756809795139083)
    ·
      refine ⟨195954679003135214692708625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130636452668756809795139083 195954679003135214692708625)
      ·
        refine ⟨146966009252351411019531469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195954679003135214692708625 146966009252351411019531469)
        ·
          refine ⟨55112253469631779132324301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146966009252351411019531469 55112253469631779132324301)
          ·
            refine ⟨20667095051111917174621613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55112253469631779132324301 20667095051111917174621613)
            ·
              refine ⟨7750160644166968940483105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20667095051111917174621613 7750160644166968940483105)
              ·
                refine ⟨5812620483125226705362329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7750160644166968940483105 5812620483125226705362329)
                ·
                  refine ⟨4359465362343920029021747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5812620483125226705362329 4359465362343920029021747)
                  ·
                    refine ⟨6539198043515880043532621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4359465362343920029021747 6539198043515880043532621)
                    ·
                      refine ⟨2452199266318455016324733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6539198043515880043532621 2452199266318455016324733)
                      ·
                        rfl

theorem cell23_4775641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 2, 2, 1, 3].length) (baseStart_4775641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775641 prefixEnd_4775641 := by exact prefixLift 4775641
  have htrace : WordTrace (prefixWord ++ tailWord_4775641) baseStart_4775641 baseEnd_4775641 := by
    simpa [prefixWord, tailWord_4775641, baseEnd_4775641] using wordTrace_append hprefix tailTrace_4775641
  have hstable : (prefixWord ++ tailWord_4775641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775641).length < 2 ^ (prefixWord ++ tailWord_4775641).sum := by decide
  have hdescent : baseEnd_4775641 < baseStart_4775641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775664 : List Nat := [2, 1, 1, 1, 3, 1, 2, 5, 1, 4, 2]
def baseStart_4775664 : Nat := 118140960795 + 4775664 * 2 ^ 59
def prefixEnd_4775664 : Nat := 4983230072969 + 3 ^ 40 * 4775664 * 2
def baseEnd_4775664 : Nat := 2452211076373508426337127

theorem tailTrace_4775664 : CollatzResearch.WordTrace tailWord_4775664 prefixEnd_4775664 2452211076373508426337127 := by
  unfold tailWord_4775664
  simp only [CollatzResearch.WordTrace]
  refine ⟨87091387885296210660803023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116121850513728280881070697 87091387885296210660803023)
  ·
    refine ⟨130637081827944315991204535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87091387885296210660803023 130637081827944315991204535)
    ·
      refine ⟨195955622741916473986806803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130637081827944315991204535 195955622741916473986806803)
      ·
        refine ⟨293933434112874710980210205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195955622741916473986806803 293933434112874710980210205)
        ·
          refine ⟨110225037792328016617578827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 293933434112874710980210205 110225037792328016617578827)
          ·
            refine ⟨165337556688492024926368241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110225037792328016617578827 165337556688492024926368241)
            ·
              refine ⟨124003167516369018694776181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165337556688492024926368241 124003167516369018694776181)
              ·
                refine ⟨11625296954659595502635267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 124003167516369018694776181 11625296954659595502635267)
                ·
                  refine ⟨17437945431989393253952901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11625296954659595502635267 17437945431989393253952901)
                  ·
                    refine ⟨3269614768498011235116169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17437945431989393253952901 3269614768498011235116169)
                    ·
                      refine ⟨2452211076373508426337127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3269614768498011235116169 2452211076373508426337127)
                      ·
                        rfl

theorem cell23_4775664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 1, 4, 2].length) (baseStart_4775664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775664 prefixEnd_4775664 := by exact prefixLift 4775664
  have htrace : WordTrace (prefixWord ++ tailWord_4775664) baseStart_4775664 baseEnd_4775664 := by
    simpa [prefixWord, tailWord_4775664, baseEnd_4775664] using wordTrace_append hprefix tailTrace_4775664
  have hstable : (prefixWord ++ tailWord_4775664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775664).length < 2 ^ (prefixWord ++ tailWord_4775664).sum := by decide
  have hdescent : baseEnd_4775664 < baseStart_4775664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775667 : List Nat := [1, 1, 1, 2, 2, 3, 2, 2, 2, 4, 3]
def baseStart_4775667 : Nat := 118140960795 + 4775667 * 2 ^ 59
def prefixEnd_4775667 : Nat := 4983230072969 + 3 ^ 40 * 4775667 * 2
def baseEnd_4775667 : Nat := 2452212616815471914599613

theorem tailTrace_4775667 : CollatzResearch.WordTrace tailWord_4775667 prefixEnd_4775667 2452212616815471914599613 := by
  unfold tailWord_4775667
  simp only [CollatzResearch.WordTrace]
  refine ⟨174182885189581552833965255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116121923459721035222643503 174182885189581552833965255)
  ·
    refine ⟨261274327784372329250947883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174182885189581552833965255 261274327784372329250947883)
    ·
      refine ⟨391911491676558493876421825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261274327784372329250947883 391911491676558493876421825)
      ·
        refine ⟨293933618757418870407316369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 391911491676558493876421825 293933618757418870407316369)
        ·
          refine ⟨220450214068064152805487277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 293933618757418870407316369 220450214068064152805487277)
          ·
            refine ⟨82668830275524057302057729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 220450214068064152805487277 82668830275524057302057729)
            ·
              refine ⟨62001622706643042976543297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82668830275524057302057729 62001622706643042976543297)
              ·
                refine ⟨46501217029982282232407473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62001622706643042976543297 46501217029982282232407473)
                ·
                  refine ⟨34875912772486711674305605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46501217029982282232407473 34875912772486711674305605)
                  ·
                    refine ⟨6539233644841258438932301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34875912772486711674305605 6539233644841258438932301)
                    ·
                      refine ⟨2452212616815471914599613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6539233644841258438932301 2452212616815471914599613)
                      ·
                        rfl

theorem cell23_4775667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 4, 3].length) (baseStart_4775667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775667 prefixEnd_4775667 := by exact prefixLift 4775667
  have htrace : WordTrace (prefixWord ++ tailWord_4775667) baseStart_4775667 baseEnd_4775667 := by
    simpa [prefixWord, tailWord_4775667, baseEnd_4775667] using wordTrace_append hprefix tailTrace_4775667
  have hstable : (prefixWord ++ tailWord_4775667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775667).length < 2 ^ (prefixWord ++ tailWord_4775667).sum := by decide
  have hdescent : baseEnd_4775667 < baseStart_4775667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775677 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 4, 2, 4]
def baseStart_4775677 : Nat := 118140960795 + 4775677 * 2 ^ 59
def prefixEnd_4775677 : Nat := 4983230072969 + 3 ^ 40 * 4775677 * 2
def baseEnd_4775677 : Nat := 2452217751622016875474567

theorem tailTrace_4775677 : CollatzResearch.WordTrace tailWord_4775677 prefixEnd_4775677 2452217751622016875474567 := by
  unfold tailWord_4775677
  simp only [CollatzResearch.WordTrace]
  refine ⟨174183249919545324541829285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116122166613030216361219523 174183249919545324541829285)
  ·
    refine ⟨32659359359914748351592991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174183249919545324541829285 32659359359914748351592991)
    ·
      refine ⟨48989039039872122527389487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32659359359914748351592991 48989039039872122527389487)
      ·
        refine ⟨73483558559808183791084231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48989039039872122527389487 73483558559808183791084231)
        ·
          refine ⟨110225337839712275686626347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73483558559808183791084231 110225337839712275686626347)
          ·
            refine ⟨165338006759568413529939521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110225337839712275686626347 165338006759568413529939521)
            ·
              refine ⟨124003505069676310147454641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165338006759568413529939521 124003505069676310147454641)
              ·
                refine ⟨93002628802257232610590981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124003505069676310147454641 93002628802257232610590981)
                ·
                  refine ⟨17437992900423231114485809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93002628802257232610590981 17437992900423231114485809)
                  ·
                    refine ⟨13078494675317423335864357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17437992900423231114485809 13078494675317423335864357)
                    ·
                      refine ⟨2452217751622016875474567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13078494675317423335864357 2452217751622016875474567)
                      ·
                        rfl

theorem cell23_4775677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_4775677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775677 prefixEnd_4775677 := by exact prefixLift 4775677
  have htrace : WordTrace (prefixWord ++ tailWord_4775677) baseStart_4775677 baseEnd_4775677 := by
    simpa [prefixWord, tailWord_4775677, baseEnd_4775677] using wordTrace_append hprefix tailTrace_4775677
  have hstable : (prefixWord ++ tailWord_4775677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775677).length < 2 ^ (prefixWord ++ tailWord_4775677).sum := by decide
  have hdescent : baseEnd_4775677 < baseStart_4775677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775681 : List Nat := [1, 2, 4, 1, 1, 1, 3, 2, 4, 2, 2]
def baseStart_4775681 : Nat := 118140960795 + 4775681 * 2 ^ 59
def prefixEnd_4775681 : Nat := 4983230072969 + 3 ^ 40 * 4775681 * 2
def baseEnd_4775681 : Nat := 2452219805544634859824549

theorem tailTrace_4775681 : CollatzResearch.WordTrace tailWord_4775681 prefixEnd_4775681 2452219805544634859824549 := by
  unfold tailWord_4775681
  simp only [CollatzResearch.WordTrace]
  refine ⟨174183395811530833224974897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116122263874353888816649931 174183395811530833224974897)
  ·
    refine ⟨130637546858648124918731173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174183395811530833224974897 130637546858648124918731173)
    ·
      refine ⟨24494540035996523422262095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130637546858648124918731173 24494540035996523422262095)
      ·
        refine ⟨36741810053994785133393143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24494540035996523422262095 36741810053994785133393143)
        ·
          refine ⟨55112715080992177700089715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36741810053994785133393143 55112715080992177700089715)
          ·
            refine ⟨82669072621488266550134573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55112715080992177700089715 82669072621488266550134573)
            ·
              refine ⟨31000902233058099956300465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82669072621488266550134573 31000902233058099956300465)
              ·
                refine ⟨23250676674793574967225349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31000902233058099956300465 23250676674793574967225349)
                ·
                  refine ⟨4359501876523795306354753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23250676674793574967225349 4359501876523795306354753)
                  ·
                    refine ⟨3269626407392846479766065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4359501876523795306354753 3269626407392846479766065)
                    ·
                      refine ⟨2452219805544634859824549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3269626407392846479766065 2452219805544634859824549)
                      ·
                        rfl

theorem cell23_4775681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 4, 2, 2].length) (baseStart_4775681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775681 prefixEnd_4775681 := by exact prefixLift 4775681
  have htrace : WordTrace (prefixWord ++ tailWord_4775681) baseStart_4775681 baseEnd_4775681 := by
    simpa [prefixWord, tailWord_4775681, baseEnd_4775681] using wordTrace_append hprefix tailTrace_4775681
  have hstable : (prefixWord ++ tailWord_4775681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775681).length < 2 ^ (prefixWord ++ tailWord_4775681).sum := by decide
  have hdescent : baseEnd_4775681 < baseStart_4775681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775684 : List Nat := [2, 3, 2, 2, 1, 3, 1, 1, 2, 1, 5]
def baseStart_4775684 : Nat := 118140960795 + 4775684 * 2 ^ 59
def prefixEnd_4775684 : Nat := 4983230072969 + 3 ^ 40 * 4775684 * 2
def baseEnd_4775684 : Nat := 2452221345986598348087035

theorem tailTrace_4775684 : CollatzResearch.WordTrace tailWord_4775684 prefixEnd_4775684 2452221345986598348087035 := by
  unfold tailWord_4775684
  simp only [CollatzResearch.WordTrace]
  refine ⟨87091752615259982368667053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116122336820346643158222737 87091752615259982368667053)
  ·
    refine ⟨32659407230722493388250145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87091752615259982368667053 32659407230722493388250145)
    ·
      refine ⟨24494555423041870041187609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32659407230722493388250145 24494555423041870041187609)
      ·
        refine ⟨18370916567281402530890707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24494555423041870041187609 18370916567281402530890707)
        ·
          refine ⟨27556374850922103796336061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18370916567281402530890707 27556374850922103796336061)
          ·
            refine ⟨10333640569095788923626023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27556374850922103796336061 10333640569095788923626023)
            ·
              refine ⟨15500460853643683385439035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10333640569095788923626023 15500460853643683385439035)
              ·
                refine ⟨23250691280465525078158553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15500460853643683385439035 23250691280465525078158553)
                ·
                  refine ⟨17438018460349143808618915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23250691280465525078158553 17438018460349143808618915)
                  ·
                    refine ⟨26157027690523715712928373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17438018460349143808618915 26157027690523715712928373)
                    ·
                      refine ⟨2452221345986598348087035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26157027690523715712928373 2452221345986598348087035)
                      ·
                        rfl

theorem cell23_4775684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_4775684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775684 prefixEnd_4775684 := by exact prefixLift 4775684
  have htrace : WordTrace (prefixWord ++ tailWord_4775684) baseStart_4775684 baseEnd_4775684 := by
    simpa [prefixWord, tailWord_4775684, baseEnd_4775684] using wordTrace_append hprefix tailTrace_4775684
  have hstable : (prefixWord ++ tailWord_4775684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775684).length < 2 ^ (prefixWord ++ tailWord_4775684).sum := by decide
  have hdescent : baseEnd_4775684 < baseStart_4775684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775693 : List Nat := [1, 7, 2, 1, 1, 1, 3, 2, 1, 2, 2]
def baseStart_4775693 : Nat := 118140960795 + 4775693 * 2 ^ 59
def prefixEnd_4775693 : Nat := 4983230072969 + 3 ^ 40 * 4775693 * 2
def baseEnd_4775693 : Nat := 2452225967312488812874495

theorem tailTrace_4775693 : CollatzResearch.WordTrace tailWord_4775693 prefixEnd_4775693 2452225967312488812874495 := by
  unfold tailWord_4775693
  simp only [CollatzResearch.WordTrace]
  refine ⟨174183833487487359274411733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116122555658324906182941155 174183833487487359274411733)
  ·
    refine ⟨4082433597362984982994025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 174183833487487359274411733 4082433597362984982994025)
    ·
      refine ⟨3061825198022238737245519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4082433597362984982994025 3061825198022238737245519)
      ·
        refine ⟨4592737797033358105868279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3061825198022238737245519 4592737797033358105868279)
        ·
          refine ⟨6889106695550037158802419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4592737797033358105868279 6889106695550037158802419)
          ·
            refine ⟨10333660043325055738203629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6889106695550037158802419 10333660043325055738203629)
            ·
              refine ⟨3875122516246895901826361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10333660043325055738203629 3875122516246895901826361)
              ·
                refine ⟨2906341887185171926369771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3875122516246895901826361 2906341887185171926369771)
                ·
                  refine ⟨4359512830777757889554657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2906341887185171926369771 4359512830777757889554657)
                  ·
                    refine ⟨3269634623083318417165993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4359512830777757889554657 3269634623083318417165993)
                    ·
                      refine ⟨2452225967312488812874495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3269634623083318417165993 2452225967312488812874495)
                      ·
                        rfl

theorem cell23_4775693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_4775693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775693 prefixEnd_4775693 := by exact prefixLift 4775693
  have htrace : WordTrace (prefixWord ++ tailWord_4775693) baseStart_4775693 baseEnd_4775693 := by
    simpa [prefixWord, tailWord_4775693, baseEnd_4775693] using wordTrace_append hprefix tailTrace_4775693
  have hstable : (prefixWord ++ tailWord_4775693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775693).length < 2 ^ (prefixWord ++ tailWord_4775693).sum := by decide
  have hdescent : baseEnd_4775693 < baseStart_4775693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775704 : List Nat := [2, 1, 2, 3, 1, 1, 2, 6, 5]
def baseStart_4775704 : Nat := 118140960795 + 4775704 * 2 ^ 59
def prefixEnd_4775704 : Nat := 4983230072969 + 3 ^ 40 * 4775704 * 2
def baseEnd_4775704 : Nat := 272470179511076474426327

theorem tailTrace_4775704 : CollatzResearch.WordTrace tailWord_4775704 prefixEnd_4775704 272470179511076474426327 := by
  unfold tailWord_4775704
  simp only [CollatzResearch.WordTrace]
  refine ⟨87092117345223754076531083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116122823126965005435374777 87092117345223754076531083)
  ·
    refine ⟨130638176017835631114796625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87092117345223754076531083 130638176017835631114796625)
    ·
      refine ⟨97978632013376723336097469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130638176017835631114796625 97978632013376723336097469)
      ·
        refine ⟨36741987005016271251036551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97978632013376723336097469 36741987005016271251036551)
        ·
          refine ⟨55112980507524406876554827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36741987005016271251036551 55112980507524406876554827)
          ·
            refine ⟨82669470761286610314832241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55112980507524406876554827 82669470761286610314832241)
            ·
              refine ⟨62002103070964957736124181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82669470761286610314832241 62002103070964957736124181)
              ·
                refine ⟨2906348581451482393880821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 62002103070964957736124181 2906348581451482393880821)
                ·
                  refine ⟨272470179511076474426327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2906348581451482393880821 272470179511076474426327)
                  ·
                    rfl

theorem cell23_4775704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 6, 5].length) (baseStart_4775704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775704 prefixEnd_4775704 := by exact prefixLift 4775704
  have htrace : WordTrace (prefixWord ++ tailWord_4775704) baseStart_4775704 baseEnd_4775704 := by
    simpa [prefixWord, tailWord_4775704, baseEnd_4775704] using wordTrace_append hprefix tailTrace_4775704
  have hstable : (prefixWord ++ tailWord_4775704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775704).length < 2 ^ (prefixWord ++ tailWord_4775704).sum := by decide
  have hdescent : baseEnd_4775704 < baseStart_4775704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775714 : List Nat := [3, 3, 1, 1, 2, 1, 2, 1, 1, 5, 3]
def baseStart_4775714 : Nat := 118140960795 + 4775714 * 2 ^ 59
def prefixEnd_4775714 : Nat := 4983230072969 + 3 ^ 40 * 4775714 * 2
def baseEnd_4775714 : Nat := 2452236750406233230711897

theorem tailTrace_4775714 : CollatzResearch.WordTrace tailWord_4775714 prefixEnd_4775714 2452236750406233230711897 := by
  unfold tailWord_4775714
  simp only [CollatzResearch.WordTrace]
  refine ⟨43546149855102819965231549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116123066280274186573950797 43546149855102819965231549)
  ·
    refine ⟨16329806195663557486961831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43546149855102819965231549 16329806195663557486961831)
    ·
      refine ⟨24494709293495336230442747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16329806195663557486961831 24494709293495336230442747)
      ·
        refine ⟨36742063940243004345664121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24494709293495336230442747 36742063940243004345664121)
        ·
          refine ⟨27556547955182253259248091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36742063940243004345664121 27556547955182253259248091)
          ·
            refine ⟨41334821932773379888872137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27556547955182253259248091 41334821932773379888872137)
            ·
              refine ⟨31001116449580034916654103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41334821932773379888872137 31001116449580034916654103)
              ·
                refine ⟨46501674674370052374981155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31001116449580034916654103 46501674674370052374981155)
                ·
                  refine ⟨69752512011555078562471733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46501674674370052374981155 69752512011555078562471733)
                  ·
                    refine ⟨6539298001083288615231725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 69752512011555078562471733 6539298001083288615231725)
                    ·
                      refine ⟨2452236750406233230711897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6539298001083288615231725 2452236750406233230711897)
                      ·
                        rfl

theorem cell23_4775714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_4775714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775714 prefixEnd_4775714 := by exact prefixLift 4775714
  have htrace : WordTrace (prefixWord ++ tailWord_4775714) baseStart_4775714 baseEnd_4775714 := by
    simpa [prefixWord, tailWord_4775714, baseEnd_4775714] using wordTrace_append hprefix tailTrace_4775714
  have hstable : (prefixWord ++ tailWord_4775714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775714).length < 2 ^ (prefixWord ++ tailWord_4775714).sum := by decide
  have hdescent : baseEnd_4775714 < baseStart_4775714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775754 : List Nat := [3, 1, 2, 1, 1, 1, 3, 4, 2, 1, 4]
def baseStart_4775754 : Nat := 118140960795 + 4775754 * 2 ^ 59
def prefixEnd_4775754 : Nat := 4983230072969 + 3 ^ 40 * 4775754 * 2
def baseEnd_4775754 : Nat := 2452257289632413074211713

theorem tailTrace_4775754 : CollatzResearch.WordTrace tailWord_4775754 prefixEnd_4775754 2452257289632413074211713 := by
  unfold tailWord_4775754
  simp only [CollatzResearch.WordTrace]
  refine ⟨43546514585066591673095579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116124038893510911128254877 43546514585066591673095579)
  ·
    refine ⟨65319771877599887509643369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43546514585066591673095579 65319771877599887509643369)
    ·
      refine ⟨48989828908199915632232527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65319771877599887509643369 48989828908199915632232527)
      ·
        refine ⟨73484743362299873448348791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48989828908199915632232527 73484743362299873448348791)
        ·
          refine ⟨110227115043449810172523187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73484743362299873448348791 110227115043449810172523187)
          ·
            refine ⟨165340672565174715258784781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110227115043449810172523187 165340672565174715258784781)
            ·
              refine ⟨62002752211940518222044293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 165340672565174715258784781 62002752211940518222044293)
              ·
                refine ⟨11625516039738847166633305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62002752211940518222044293 11625516039738847166633305)
                ·
                  refine ⟨8719137029804135374974979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11625516039738847166633305 8719137029804135374974979)
                  ·
                    refine ⟨13078705544706203062462469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8719137029804135374974979 13078705544706203062462469)
                    ·
                      refine ⟨2452257289632413074211713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13078705544706203062462469 2452257289632413074211713)
                      ·
                        rfl

theorem cell23_4775754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_4775754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775754 prefixEnd_4775754 := by exact prefixLift 4775754
  have htrace : WordTrace (prefixWord ++ tailWord_4775754) baseStart_4775754 baseEnd_4775754 := by
    simpa [prefixWord, tailWord_4775754, baseEnd_4775754] using wordTrace_append hprefix tailTrace_4775754
  have hstable : (prefixWord ++ tailWord_4775754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775754).length < 2 ^ (prefixWord ++ tailWord_4775754).sum := by decide
  have hdescent : baseEnd_4775754 < baseStart_4775754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775811 : List Nat := [1, 1, 1, 3, 4, 4, 1, 2, 6]
def baseStart_4775811 : Nat := 118140960795 + 4775811 * 2 ^ 59
def prefixEnd_4775811 : Nat := 4983230072969 + 3 ^ 40 * 4775811 * 2
def baseEnd_4775811 : Nat := 272476284225524372355439

theorem tailTrace_4775811 : CollatzResearch.WordTrace tailWord_4775811 prefixEnd_4775811 272476284225524372355439 := by
  unfold tailWord_4775811
  simp only [CollatzResearch.WordTrace]
  refine ⟨174188137301059865427207287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116125424867373243618138191 174188137301059865427207287)
  ·
    refine ⟨261282205951589798140810931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174188137301059865427207287 261282205951589798140810931)
    ·
      refine ⟨391923308927384697211216397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261282205951589798140810931 391923308927384697211216397)
      ·
        refine ⟨146971240847769261454206149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 391923308927384697211216397 146971240847769261454206149)
        ·
          refine ⟨27557107658956736522663653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 146971240847769261454206149 27557107658956736522663653)
          ·
            refine ⟨5166957686054388097999435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27557107658956736522663653 5166957686054388097999435)
            ·
              refine ⟨7750436529081582146999153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5166957686054388097999435 7750436529081582146999153)
              ·
                refine ⟨5812827396811186610249365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7750436529081582146999153 5812827396811186610249365)
                ·
                  refine ⟨272476284225524372355439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5812827396811186610249365 272476284225524372355439)
                  ·
                    rfl

theorem cell23_4775811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 2, 6].length) (baseStart_4775811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775811 prefixEnd_4775811 := by exact prefixLift 4775811
  have htrace : WordTrace (prefixWord ++ tailWord_4775811) baseStart_4775811 baseEnd_4775811 := by
    simpa [prefixWord, tailWord_4775811, baseEnd_4775811] using wordTrace_append hprefix tailTrace_4775811
  have hstable : (prefixWord ++ tailWord_4775811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775811).length < 2 ^ (prefixWord ++ tailWord_4775811).sum := by decide
  have hdescent : baseEnd_4775811 < baseStart_4775811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775828 : List Nat := [2, 4, 2, 1, 1, 3, 3, 1, 6]
def baseStart_4775828 : Nat := 118140960795 + 4775828 * 2 ^ 59
def prefixEnd_4775828 : Nat := 4983230072969 + 3 ^ 40 * 4775828 * 2
def baseEnd_4775828 : Nat := 272477254133427309409597

theorem tailTrace_4775828 : CollatzResearch.WordTrace tailWord_4775828 prefixEnd_4775828 272477254133427309409597 := by
  unfold tailWord_4775828
  simp only [CollatzResearch.WordTrace]
  refine ⟨87094378670999138665288069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116125838227998851553717425 87094378670999138665288069)
  ·
    refine ⟨16330196000812338499741513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87094378670999138665288069 16330196000812338499741513)
    ·
      refine ⟨12247647000609253874806135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16330196000812338499741513 12247647000609253874806135)
      ·
        refine ⟨18371470500913880812209203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12247647000609253874806135 18371470500913880812209203)
        ·
          refine ⟨27557205751370821218313805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18371470500913880812209203 27557205751370821218313805)
          ·
            refine ⟨10333952156764057956867677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27557205751370821218313805 10333952156764057956867677)
            ·
              refine ⟨3875232058786521733825379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10333952156764057956867677 3875232058786521733825379)
              ·
                refine ⟨5812848088179782600738069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3875232058786521733825379 5812848088179782600738069)
                ·
                  refine ⟨272477254133427309409597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5812848088179782600738069 272477254133427309409597)
                  ·
                    rfl

theorem cell23_4775828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_4775828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775828 prefixEnd_4775828 := by exact prefixLift 4775828
  have htrace : WordTrace (prefixWord ++ tailWord_4775828) baseStart_4775828 baseEnd_4775828 := by
    simpa [prefixWord, tailWord_4775828, baseEnd_4775828] using wordTrace_append hprefix tailTrace_4775828
  have hstable : (prefixWord ++ tailWord_4775828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775828).length < 2 ^ (prefixWord ++ tailWord_4775828).sum := by decide
  have hdescent : baseEnd_4775828 < baseStart_4775828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775831 : List Nat := [1, 1, 3, 3, 1, 3, 1, 2, 1, 5, 2]
def baseStart_4775831 : Nat := 118140960795 + 4775831 * 2 ^ 59
def prefixEnd_4775831 : Nat := 4983230072969 + 3 ^ 40 * 4775831 * 2
def baseEnd_4775831 : Nat := 2452296827642809272948859

theorem tailTrace_4775831 : CollatzResearch.WordTrace tailWord_4775831 prefixEnd_4775831 2452296827642809272948859 := by
  unfold tailWord_4775831
  simp only [CollatzResearch.WordTrace]
  refine ⟨174188866760987408842935347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116125911173991605895290231 174188866760987408842935347)
  ·
    refine ⟨261283300141481113264403021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174188866760987408842935347 261283300141481113264403021)
    ·
      refine ⟨97981237553055417474151133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 261283300141481113264403021 97981237553055417474151133)
      ·
        refine ⟨36742964082395781552806675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97981237553055417474151133 36742964082395781552806675)
        ·
          refine ⟨55114446123593672329210013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36742964082395781552806675 55114446123593672329210013)
          ·
            refine ⟨20667917296347627123453755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55114446123593672329210013 20667917296347627123453755)
            ·
              refine ⟨31001875944521440685180633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20667917296347627123453755 31001875944521440685180633)
              ·
                refine ⟨23251406958391080513885475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31001875944521440685180633 23251406958391080513885475)
                ·
                  refine ⟨34877110437586620770828213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23251406958391080513885475 34877110437586620770828213)
                  ·
                    refine ⟨3269729103523745697265145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34877110437586620770828213 3269729103523745697265145)
                    ·
                      refine ⟨2452296827642809272948859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3269729103523745697265145 2452296827642809272948859)
                      ·
                        rfl

theorem cell23_4775831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 5, 2].length) (baseStart_4775831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775831 prefixEnd_4775831 := by exact prefixLift 4775831
  have htrace : WordTrace (prefixWord ++ tailWord_4775831) baseStart_4775831 baseEnd_4775831 := by
    simpa [prefixWord, tailWord_4775831, baseEnd_4775831] using wordTrace_append hprefix tailTrace_4775831
  have hstable : (prefixWord ++ tailWord_4775831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775831).length < 2 ^ (prefixWord ++ tailWord_4775831).sum := by decide
  have hdescent : baseEnd_4775831 < baseStart_4775831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775871 : List Nat := [1, 1, 2, 2, 2, 1, 4, 4, 2, 4]
def baseStart_4775871 : Nat := 118140960795 + 4775871 * 2 ^ 59
def prefixEnd_4775871 : Nat := 4983230072969 + 3 ^ 40 * 4775871 * 2
def baseEnd_4775871 : Nat := 817439122289663038816225

theorem tailTrace_4775871 : CollatzResearch.WordTrace tailWord_4775871 prefixEnd_4775871 817439122289663038816225 := by
  unfold tailWord_4775871
  simp only [CollatzResearch.WordTrace]
  refine ⟨174190325680842495674391467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116126883787228330449594311 174190325680842495674391467)
  ·
    refine ⟨261285488521263743511587201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174190325680842495674391467 261285488521263743511587201)
    ·
      refine ⟨195964116390947807633690401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261285488521263743511587201 195964116390947807633690401)
      ·
        refine ⟨146973087293210855725267801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195964116390947807633690401 146973087293210855725267801)
        ·
          refine ⟨110229815469908141793950851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146973087293210855725267801 110229815469908141793950851)
          ·
            refine ⟨165344723204862212690926277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110229815469908141793950851 165344723204862212690926277)
            ·
              refine ⟨31002135600911664879548677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 165344723204862212690926277 31002135600911664879548677)
              ·
                refine ⟨5812900425170937164915377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31002135600911664879548677 5812900425170937164915377)
                ·
                  refine ⟨4359675318878202873686533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5812900425170937164915377 4359675318878202873686533)
                  ·
                    refine ⟨817439122289663038816225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4359675318878202873686533 817439122289663038816225)
                    ·
                      rfl

theorem cell23_4775871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 4, 2, 4].length) (baseStart_4775871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775871 prefixEnd_4775871 := by exact prefixLift 4775871
  have htrace : WordTrace (prefixWord ++ tailWord_4775871) baseStart_4775871 baseEnd_4775871 := by
    simpa [prefixWord, tailWord_4775871, baseEnd_4775871] using wordTrace_append hprefix tailTrace_4775871
  have hstable : (prefixWord ++ tailWord_4775871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775871).length < 2 ^ (prefixWord ++ tailWord_4775871).sum := by decide
  have hdescent : baseEnd_4775871 < baseStart_4775871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775884 : List Nat := [2, 2, 1, 4, 1, 2, 1, 10]
def baseStart_4775884 : Nat := 118140960795 + 4775884 * 2 ^ 59
def prefixEnd_4775884 : Nat := 4983230072969 + 3 ^ 40 * 4775884 * 2
def baseEnd_4775884 : Nat := 90826816374722132058745

theorem tailTrace_4775884 : CollatzResearch.WordTrace tailWord_4775884 prefixEnd_4775884 90826816374722132058745 := by
  unfold tailWord_4775884
  simp only [CollatzResearch.WordTrace]
  refine ⟨87095399914897699447307353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116127199886530265929743137 87095399914897699447307353)
  ·
    refine ⟨65321549936173274585480515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87095399914897699447307353 65321549936173274585480515)
    ·
      refine ⟨97982324904259911878220773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65321549936173274585480515 97982324904259911878220773)
      ·
        refine ⟨18371685919548733477166395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97982324904259911878220773 18371685919548733477166395)
        ·
          refine ⟨27557528879323100215749593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18371685919548733477166395 27557528879323100215749593)
          ·
            refine ⟨20668146659492325161812195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27557528879323100215749593 20668146659492325161812195)
            ·
              refine ⟨31002219989238487742718293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20668146659492325161812195 31002219989238487742718293)
              ·
                refine ⟨90826816374722132058745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 31002219989238487742718293 90826816374722132058745)
                ·
                  rfl

theorem cell23_4775884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 10].length) (baseStart_4775884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775884 prefixEnd_4775884 := by exact prefixLift 4775884
  have htrace : WordTrace (prefixWord ++ tailWord_4775884) baseStart_4775884 baseEnd_4775884 := by
    simpa [prefixWord, tailWord_4775884, baseEnd_4775884] using wordTrace_append hprefix tailTrace_4775884
  have hstable : (prefixWord ++ tailWord_4775884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775884).length < 2 ^ (prefixWord ++ tailWord_4775884).sum := by decide
  have hdescent : baseEnd_4775884 < baseStart_4775884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775888 : List Nat := [2, 1, 1, 1, 1, 2, 8, 1, 2, 4]
def baseStart_4775888 : Nat := 118140960795 + 4775888 * 2 ^ 59
def prefixEnd_4775888 : Nat := 4983230072969 + 3 ^ 40 * 4775888 * 2
def baseEnd_4775888 : Nat := 817442032013371849978699

theorem tailTrace_4775888 : CollatzResearch.WordTrace tailWord_4775888 prefixEnd_4775888 817442032013371849978699 := by
  unfold tailWord_4775888
  simp only [CollatzResearch.WordTrace]
  refine ⟨87095472860890453788880159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116127297147853938385173545 87095472860890453788880159)
  ·
    refine ⟨130643209291335680683320239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87095472860890453788880159 130643209291335680683320239)
    ·
      refine ⟨195964813937003521024980359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130643209291335680683320239 195964813937003521024980359)
      ·
        refine ⟨293947220905505281537470539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195964813937003521024980359 293947220905505281537470539)
        ·
          refine ⟨440920831358257922306205809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293947220905505281537470539 440920831358257922306205809)
          ·
            refine ⟨330690623518693441729654357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 440920831358257922306205809 330690623518693441729654357)
            ·
              refine ⟨3875280744359688770269387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 330690623518693441729654357 3875280744359688770269387)
              ·
                refine ⟨5812921116539533155404081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3875280744359688770269387 5812921116539533155404081)
                ·
                  refine ⟨4359690837404649866553061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5812921116539533155404081 4359690837404649866553061)
                  ·
                    refine ⟨817442032013371849978699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4359690837404649866553061 817442032013371849978699)
                    ·
                      rfl

theorem cell23_4775888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 1, 2, 4].length) (baseStart_4775888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775888 prefixEnd_4775888 := by exact prefixLift 4775888
  have htrace : WordTrace (prefixWord ++ tailWord_4775888) baseStart_4775888 baseEnd_4775888 := by
    simpa [prefixWord, tailWord_4775888, baseEnd_4775888] using wordTrace_append hprefix tailTrace_4775888
  have hstable : (prefixWord ++ tailWord_4775888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775888).length < 2 ^ (prefixWord ++ tailWord_4775888).sum := by decide
  have hdescent : baseEnd_4775888 < baseStart_4775888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775898 : List Nat := [3, 1, 1, 2, 5, 1, 1, 1, 3, 2, 3]
def baseStart_4775898 : Nat := 118140960795 + 4775898 * 2 ^ 59
def prefixEnd_4775898 : Nat := 4983230072969 + 3 ^ 40 * 4775898 * 2
def baseEnd_4775898 : Nat := 2452331230846660510811051

theorem tailTrace_4775898 : CollatzResearch.WordTrace tailWord_4775898 prefixEnd_4775898 2452331230846660510811051 := by
  unfold tailWord_4775898
  simp only [CollatzResearch.WordTrace]
  refine ⟨43547827612936169821406087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116127540301163119523749565 43547827612936169821406087)
  ·
    refine ⟨65321741419404254732109131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43547827612936169821406087 65321741419404254732109131)
    ·
      refine ⟨97982612129106382098163697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65321741419404254732109131 97982612129106382098163697)
      ·
        refine ⟨73486959096829786573622773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97982612129106382098163697 73486959096829786573622773)
        ·
          refine ⟨6889402415327792491277135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73486959096829786573622773 6889402415327792491277135)
          ·
            refine ⟨10334103622991688736915703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6889402415327792491277135 10334103622991688736915703)
            ·
              refine ⟨15501155434487533105373555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10334103622991688736915703 15501155434487533105373555)
              ·
                refine ⟨23251733151731299658060333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15501155434487533105373555 23251733151731299658060333)
                ·
                  refine ⟨8719399931899237371772625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23251733151731299658060333 8719399931899237371772625)
                  ·
                    refine ⟨6539549948924428028829469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8719399931899237371772625 6539549948924428028829469)
                    ·
                      refine ⟨2452331230846660510811051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6539549948924428028829469 2452331230846660510811051)
                      ·
                        rfl

theorem cell23_4775898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 3, 2, 3].length) (baseStart_4775898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775898 prefixEnd_4775898 := by exact prefixLift 4775898
  have htrace : WordTrace (prefixWord ++ tailWord_4775898) baseStart_4775898 baseEnd_4775898 := by
    simpa [prefixWord, tailWord_4775898, baseEnd_4775898] using wordTrace_append hprefix tailTrace_4775898
  have hstable : (prefixWord ++ tailWord_4775898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775898).length < 2 ^ (prefixWord ++ tailWord_4775898).sum := by decide
  have hdescent : baseEnd_4775898 < baseStart_4775898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775928 : List Nat := [2, 1, 2, 1, 1, 3, 3, 4, 2, 1, 3]
def baseStart_4775928 : Nat := 118140960795 + 4775928 * 2 ^ 59
def prefixEnd_4775928 : Nat := 4983230072969 + 3 ^ 40 * 4775928 * 2
def baseEnd_4775928 : Nat := 2452346635266295393435913

theorem tailTrace_4775928 : CollatzResearch.WordTrace tailWord_4775928 prefixEnd_4775928 2452346635266295393435913 := by
  unfold tailWord_4775928
  simp only [CollatzResearch.WordTrace]
  refine ⟨87096202320817997204608219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116128269761090662939477625 87096202320817997204608219)
  ·
    refine ⟨130644303481226995806912329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87096202320817997204608219 130644303481226995806912329)
    ·
      refine ⟨97983227610920246855184247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130644303481226995806912329 97983227610920246855184247)
      ·
        refine ⟨146974841416380370282776371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97983227610920246855184247 146974841416380370282776371)
        ·
          refine ⟨220462262124570555424164557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146974841416380370282776371 220462262124570555424164557)
          ·
            refine ⟨82673348296713958284061709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 220462262124570555424164557 82673348296713958284061709)
            ·
              refine ⟨31002505611267734356523141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82673348296713958284061709 31002505611267734356523141)
              ·
                refine ⟨5812969802112700191848089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31002505611267734356523141 5812969802112700191848089)
                ·
                  refine ⟨4359727351584525143886067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5812969802112700191848089 4359727351584525143886067)
                  ·
                    refine ⟨6539591027376787715829101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4359727351584525143886067 6539591027376787715829101)
                    ·
                      refine ⟨2452346635266295393435913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6539591027376787715829101 2452346635266295393435913)
                      ·
                        rfl

theorem cell23_4775928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 4, 2, 1, 3].length) (baseStart_4775928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775928 prefixEnd_4775928 := by exact prefixLift 4775928
  have htrace : WordTrace (prefixWord ++ tailWord_4775928) baseStart_4775928 baseEnd_4775928 := by
    simpa [prefixWord, tailWord_4775928, baseEnd_4775928] using wordTrace_append hprefix tailTrace_4775928
  have hstable : (prefixWord ++ tailWord_4775928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775928).length < 2 ^ (prefixWord ++ tailWord_4775928).sum := by decide
  have hdescent : baseEnd_4775928 < baseStart_4775928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775929 : List Nat := [1, 2, 1, 3, 1, 6, 2, 2, 1, 2, 2]
def baseStart_4775929 : Nat := 118140960795 + 4775929 * 2 ^ 59
def prefixEnd_4775929 : Nat := 4983230072969 + 3 ^ 40 * 4775929 * 2
def baseEnd_4775929 : Nat := 2452347148746949889523409

theorem tailTrace_4775929 : CollatzResearch.WordTrace tailWord_4775929 prefixEnd_4775929 2452347148746949889523409 := by
  unfold tailWord_4775929
  simp only [CollatzResearch.WordTrace]
  refine ⟨174192441114632371580002841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116128294076421581053335227 174192441114632371580002841)
  ·
    refine ⟨130644330835974278685002131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174192441114632371580002841 130644330835974278685002131)
    ·
      refine ⟨195966496253961418027503197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130644330835974278685002131 195966496253961418027503197)
      ·
        refine ⟨73487436095235531760313699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195966496253961418027503197 73487436095235531760313699)
        ·
          refine ⟨110231154142853297640470549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73487436095235531760313699 110231154142853297640470549)
          ·
            refine ⟨5167085350446248326897057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 110231154142853297640470549 5167085350446248326897057)
            ·
              refine ⟨3875314012834686245172793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5167085350446248326897057 3875314012834686245172793)
              ·
                refine ⟨2906485509626014683879595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3875314012834686245172793 2906485509626014683879595)
                ·
                  refine ⟨4359728264439022025819393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2906485509626014683879595 4359728264439022025819393)
                  ·
                    refine ⟨3269796198329266519364545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4359728264439022025819393 3269796198329266519364545)
                    ·
                      refine ⟨2452347148746949889523409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3269796198329266519364545 2452347148746949889523409)
                      ·
                        rfl

theorem cell23_4775929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 2, 1, 2, 2].length) (baseStart_4775929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775929 prefixEnd_4775929 := by exact prefixLift 4775929
  have htrace : WordTrace (prefixWord ++ tailWord_4775929) baseStart_4775929 baseEnd_4775929 := by
    simpa [prefixWord, tailWord_4775929, baseEnd_4775929] using wordTrace_append hprefix tailTrace_4775929
  have hstable : (prefixWord ++ tailWord_4775929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775929).length < 2 ^ (prefixWord ++ tailWord_4775929).sum := by decide
  have hdescent : baseEnd_4775929 < baseStart_4775929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775972 : List Nat := [2, 3, 1, 4, 2, 1, 1, 3, 1, 3, 2]
def baseStart_4775972 : Nat := 118140960795 + 4775972 * 2 ^ 59
def prefixEnd_4775972 : Nat := 4983230072969 + 3 ^ 40 * 4775972 * 2
def baseEnd_4775972 : Nat := 2452369228415093221285711

theorem tailTrace_4775972 : CollatzResearch.WordTrace tailWord_4775972 prefixEnd_4775972 2452369228415093221285711 := by
  unfold tailWord_4775972
  simp only [CollatzResearch.WordTrace]
  refine ⟨87097004726738294961909085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116129339635651059949212113 87097004726738294961909085)
  ·
    refine ⟨32661376772526860610715907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87097004726738294961909085 32661376772526860610715907)
    ·
      refine ⟨48992065158790290916073861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32661376772526860610715907 48992065158790290916073861)
      ·
        refine ⟨9186012217273179546763849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48992065158790290916073861 9186012217273179546763849)
        ·
          refine ⟨6889509162954884660072887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9186012217273179546763849 6889509162954884660072887)
          ·
            refine ⟨10334263744432326990109331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6889509162954884660072887 10334263744432326990109331)
            ·
              refine ⟨15501395616648490485163997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10334263744432326990109331 15501395616648490485163997)
              ·
                refine ⟨5813023356243183931936499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15501395616648490485163997 5813023356243183931936499)
                ·
                  refine ⟨8719535034364775897904749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5813023356243183931936499 8719535034364775897904749)
                  ·
                    refine ⟨3269825637886790961714281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8719535034364775897904749 3269825637886790961714281)
                    ·
                      refine ⟨2452369228415093221285711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3269825637886790961714281 2452369228415093221285711)
                      ·
                        rfl

theorem cell23_4775972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_4775972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775972 prefixEnd_4775972 := by exact prefixLift 4775972
  have htrace : WordTrace (prefixWord ++ tailWord_4775972) baseStart_4775972 baseEnd_4775972 := by
    simpa [prefixWord, tailWord_4775972, baseEnd_4775972] using wordTrace_append hprefix tailTrace_4775972
  have hstable : (prefixWord ++ tailWord_4775972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775972).length < 2 ^ (prefixWord ++ tailWord_4775972).sum := by decide
  have hdescent : baseEnd_4775972 < baseStart_4775972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4775985 : List Nat := [1, 2, 2, 3, 1, 4, 1, 1, 4, 2, 2]
def baseStart_4775985 : Nat := 118140960795 + 4775985 * 2 ^ 59
def prefixEnd_4775985 : Nat := 4983230072969 + 3 ^ 40 * 4775985 * 2
def baseEnd_4775985 : Nat := 2452375903663601670423151

theorem tailTrace_4775985 : CollatzResearch.WordTrace tailWord_4775985 prefixEnd_4775985 2452375903663601670423151 := by
  unfold tailWord_4775985
  simp only [CollatzResearch.WordTrace]
  refine ⟨174194483602429493144041409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116129655734952995429360939 174194483602429493144041409)
  ·
    refine ⟨130645862701822119858031057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174194483602429493144041409 130645862701822119858031057)
    ·
      refine ⟨97984397026366589893523293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130645862701822119858031057 97984397026366589893523293)
      ·
        refine ⟨36744148884887471210071235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97984397026366589893523293 36744148884887471210071235)
        ·
          refine ⟨55116223327331206815106853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36744148884887471210071235 55116223327331206815106853)
          ·
            refine ⟨10334291873874601277832535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55116223327331206815106853 10334291873874601277832535)
            ·
              refine ⟨15501437810811901916748803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10334291873874601277832535 15501437810811901916748803)
              ·
                refine ⟨23252156716217852875123205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15501437810811901916748803 23252156716217852875123205)
                ·
                  refine ⟨4359779384290847414085601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23252156716217852875123205 4359779384290847414085601)
                  ·
                    refine ⟨3269834538218135560564201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4359779384290847414085601 3269834538218135560564201)
                    ·
                      refine ⟨2452375903663601670423151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3269834538218135560564201 2452375903663601670423151)
                      ·
                        rfl

theorem cell23_4775985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 4, 2, 2].length) (baseStart_4775985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4775985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4775985 prefixEnd_4775985 := by exact prefixLift 4775985
  have htrace : WordTrace (prefixWord ++ tailWord_4775985) baseStart_4775985 baseEnd_4775985 := by
    simpa [prefixWord, tailWord_4775985, baseEnd_4775985] using wordTrace_append hprefix tailTrace_4775985
  have hstable : (prefixWord ++ tailWord_4775985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4775985).length < 2 ^ (prefixWord ++ tailWord_4775985).sum := by decide
  have hdescent : baseEnd_4775985 < baseStart_4775985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4775985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776021 : List Nat := [1, 3, 2, 2, 1, 3, 2, 1, 1, 7]
def baseStart_4776021 : Nat := 118140960795 + 4776021 * 2 ^ 59
def prefixEnd_4776021 : Nat := 4983230072969 + 3 ^ 40 * 4776021 * 2
def baseEnd_4776021 : Nat := 817464796322387843190995

theorem tailTrace_4776021 : CollatzResearch.WordTrace tailWord_4776021 prefixEnd_4776021 817464796322387843190995 := by
  unfold tailWord_4776021
  simp only [CollatzResearch.WordTrace]
  refine ⟨174195796630299071292351917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116130531086866047528234611 174195796630299071292351917)
  ·
    refine ⟨65323423736362151734631969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174195796630299071292351917 65323423736362151734631969)
    ·
      refine ⟨48992567802271613800973977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65323423736362151734631969 48992567802271613800973977)
      ·
        refine ⟨36744425851703710350730483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48992567802271613800973977 36744425851703710350730483)
        ·
          refine ⟨55116638777555565526095725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36744425851703710350730483 55116638777555565526095725)
          ·
            refine ⟨20668739541583337072285897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55116638777555565526095725 20668739541583337072285897)
            ·
              refine ⟨15501554656187502804214423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20668739541583337072285897 15501554656187502804214423)
              ·
                refine ⟨23252331984281254206321635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15501554656187502804214423 23252331984281254206321635)
                ·
                  refine ⟨34878497976421881309482453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23252331984281254206321635 34878497976421881309482453)
                  ·
                    refine ⟨817464796322387843190995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34878497976421881309482453 817464796322387843190995)
                    ·
                      rfl

theorem cell23_4776021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_4776021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776021 prefixEnd_4776021 := by exact prefixLift 4776021
  have htrace : WordTrace (prefixWord ++ tailWord_4776021) baseStart_4776021 baseEnd_4776021 := by
    simpa [prefixWord, tailWord_4776021, baseEnd_4776021] using wordTrace_append hprefix tailTrace_4776021
  have hstable : (prefixWord ++ tailWord_4776021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776021).length < 2 ^ (prefixWord ++ tailWord_4776021).sum := by decide
  have hdescent : baseEnd_4776021 < baseStart_4776021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776042 : List Nat := [3, 1, 3, 2, 3, 1, 3, 2, 5]
def baseStart_4776042 : Nat := 118140960795 + 4776042 * 2 ^ 59
def prefixEnd_4776042 : Nat := 4983230072969 + 3 ^ 40 * 4776042 * 2
def baseEnd_4776042 : Nat := 272489463562323105267821

theorem tailTrace_4776042 : CollatzResearch.WordTrace tailWord_4776042 prefixEnd_4776042 272489463562323105267821 := by
  unfold tailWord_4776042
  simp only [CollatzResearch.WordTrace]
  refine ⟨43549140640805747969716595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116131041708815327919244253 43549140640805747969716595)
  ·
    refine ⟨65323710961208621954574893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43549140640805747969716595 65323710961208621954574893)
    ·
      refine ⟨24496391610453233232965585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65323710961208621954574893 24496391610453233232965585)
      ·
        refine ⟨18372293707839924924724189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24496391610453233232965585 18372293707839924924724189)
        ·
          refine ⟨6889610140439971846771571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18372293707839924924724189 6889610140439971846771571)
          ·
            refine ⟨10334415210659957770157357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6889610140439971846771571 10334415210659957770157357)
            ·
              refine ⟨3875405703997484163809009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10334415210659957770157357 3875405703997484163809009)
              ·
                refine ⟨2906554277998113122856757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3875405703997484163809009 2906554277998113122856757)
                ·
                  refine ⟨272489463562323105267821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2906554277998113122856757 272489463562323105267821)
                  ·
                    rfl

theorem cell23_4776042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 2, 5].length) (baseStart_4776042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776042 prefixEnd_4776042 := by exact prefixLift 4776042
  have htrace : WordTrace (prefixWord ++ tailWord_4776042) baseStart_4776042 baseEnd_4776042 := by
    simpa [prefixWord, tailWord_4776042, baseEnd_4776042] using wordTrace_append hprefix tailTrace_4776042
  have hstable : (prefixWord ++ tailWord_4776042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776042).length < 2 ^ (prefixWord ++ tailWord_4776042).sum := by decide
  have hdescent : baseEnd_4776042 < baseStart_4776042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776068 : List Nat := [2, 3, 2, 1, 2, 1, 2, 1, 5, 4]
def baseStart_4776068 : Nat := 118140960795 + 4776068 * 2 ^ 59
def prefixEnd_4776068 : Nat := 4983230072969 + 3 ^ 40 * 4776068 * 2
def baseEnd_4776068 : Nat := 817472840852641615228423

theorem tailTrace_4776068 : CollatzResearch.WordTrace tailWord_4776068 prefixEnd_4776068 817472840852641615228423 := by
  unfold tailWord_4776068
  simp only [CollatzResearch.WordTrace]
  refine ⟨87098755430564399159656429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116131673907419198879541905 87098755430564399159656429)
  ·
    refine ⟨32662033286461649684871161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87098755430564399159656429 32662033286461649684871161)
    ·
      refine ⟨24496524964846237263653371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32662033286461649684871161 24496524964846237263653371)
      ·
        refine ⟨36744787447269355895480057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24496524964846237263653371 36744787447269355895480057)
        ·
          refine ⟨27558590585452016921610043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36744787447269355895480057 27558590585452016921610043)
          ·
            refine ⟨41337885878178025382415065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27558590585452016921610043 41337885878178025382415065)
            ·
              refine ⟨31003414408633519036811299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41337885878178025382415065 31003414408633519036811299)
              ·
                refine ⟨46505121612950278555216949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31003414408633519036811299 46505121612950278555216949)
                ·
                  refine ⟨4359855151214088614551589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46505121612950278555216949 4359855151214088614551589)
                  ·
                    refine ⟨817472840852641615228423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4359855151214088614551589 817472840852641615228423)
                    ·
                      rfl

theorem cell23_4776068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_4776068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776068 prefixEnd_4776068 := by exact prefixLift 4776068
  have htrace : WordTrace (prefixWord ++ tailWord_4776068) baseStart_4776068 baseEnd_4776068 := by
    simpa [prefixWord, tailWord_4776068, baseEnd_4776068] using wordTrace_append hprefix tailTrace_4776068
  have hstable : (prefixWord ++ tailWord_4776068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776068).length < 2 ^ (prefixWord ++ tailWord_4776068).sum := by decide
  have hdescent : baseEnd_4776068 < baseStart_4776068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776071 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 2, 4, 4]
def baseStart_4776071 : Nat := 118140960795 + 4776071 * 2 ^ 59
def prefixEnd_4776071 : Nat := 4983230072969 + 3 ^ 40 * 4776071 * 2
def baseEnd_4776071 : Nat := 2452420062999888333947755

theorem tailTrace_4776071 : CollatzResearch.WordTrace tailWord_4776071 prefixEnd_4776071 2452420062999888333947755 := by
  unfold tailWord_4776071
  simp only [CollatzResearch.WordTrace]
  refine ⟨174197620280117929831672067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116131746853411953221114711 174197620280117929831672067)
  ·
    refine ⟨261296430420176894747508101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174197620280117929831672067 261296430420176894747508101)
    ·
      refine ⟨48993080703783167765157769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 261296430420176894747508101 48993080703783167765157769)
      ·
        refine ⟨36744810527837375823868327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48993080703783167765157769 36744810527837375823868327)
        ·
          refine ⟨55117215791756063735802491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36744810527837375823868327 55117215791756063735802491)
          ·
            refine ⟨82675823687634095603703737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55117215791756063735802491 82675823687634095603703737)
            ·
              refine ⟨62006867765725571702777803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82675823687634095603703737 62006867765725571702777803)
              ·
                refine ⟨93010301648588357554166705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62006867765725571702777803 93010301648588357554166705)
                ·
                  refine ⟨69757726236441268165625029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93010301648588357554166705 69757726236441268165625029)
                  ·
                    refine ⟨13079573669332737781054693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 69757726236441268165625029 13079573669332737781054693)
                    ·
                      refine ⟨2452420062999888333947755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13079573669332737781054693 2452420062999888333947755)
                      ·
                        rfl

theorem cell23_4776071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_4776071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776071 prefixEnd_4776071 := by exact prefixLift 4776071
  have htrace : WordTrace (prefixWord ++ tailWord_4776071) baseStart_4776071 baseEnd_4776071 := by
    simpa [prefixWord, tailWord_4776071, baseEnd_4776071] using wordTrace_append hprefix tailTrace_4776071
  have hstable : (prefixWord ++ tailWord_4776071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776071).length < 2 ^ (prefixWord ++ tailWord_4776071).sum := by decide
  have hdescent : baseEnd_4776071 < baseStart_4776071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776085 : List Nat := [1, 3, 2, 1, 1, 1, 4, 5, 1, 4]
def baseStart_4776085 : Nat := 118140960795 + 4776085 * 2 ^ 59
def prefixEnd_4776085 : Nat := 4983230072969 + 3 ^ 40 * 4776085 * 2
def baseEnd_4776085 : Nat := 817475750576350426390897

theorem tailTrace_4776085 : CollatzResearch.WordTrace tailWord_4776085 prefixEnd_4776085 817475750576350426390897 := by
  unfold tailWord_4776085
  simp only [CollatzResearch.WordTrace]
  refine ⟨174198130902067210222681709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116132087268044806815121139 174198130902067210222681709)
  ·
    refine ⟨65324299088275203833505641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174198130902067210222681709 65324299088275203833505641)
    ·
      refine ⟨48993224316206402875129231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65324299088275203833505641 48993224316206402875129231)
      ·
        refine ⟨73489836474309604312693847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48993224316206402875129231 73489836474309604312693847)
        ·
          refine ⟨110234754711464406469040771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73489836474309604312693847 110234754711464406469040771)
          ·
            refine ⟨165352132067196609703561157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110234754711464406469040771 165352132067196609703561157)
            ·
              refine ⟨31003524762599364319417717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 165352132067196609703561157 31003524762599364319417717)
              ·
                refine ⟨2906580446493690404945411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31003524762599364319417717 2906580446493690404945411)
                ·
                  refine ⟨4359870669740535607418117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2906580446493690404945411 4359870669740535607418117)
                  ·
                    refine ⟨817475750576350426390897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4359870669740535607418117 817475750576350426390897)
                    ·
                      rfl

theorem cell23_4776085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 5, 1, 4].length) (baseStart_4776085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776085 prefixEnd_4776085 := by exact prefixLift 4776085
  have htrace : WordTrace (prefixWord ++ tailWord_4776085) baseStart_4776085 baseEnd_4776085 := by
    simpa [prefixWord, tailWord_4776085, baseEnd_4776085] using wordTrace_append hprefix tailTrace_4776085
  have hstable : (prefixWord ++ tailWord_4776085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776085).length < 2 ^ (prefixWord ++ tailWord_4776085).sum := by decide
  have hdescent : baseEnd_4776085 < baseStart_4776085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776091 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 1, 7, 3]
def baseStart_4776091 : Nat := 118140960795 + 4776091 * 2 ^ 59
def prefixEnd_4776091 : Nat := 4983230072969 + 3 ^ 40 * 4776091 * 2
def baseEnd_4776091 : Nat := 2452430332612978255697663

theorem tailTrace_4776091 : CollatzResearch.WordTrace tailWord_4776091 prefixEnd_4776091 2452430332612978255697663 := by
  unfold tailWord_4776091
  simp only [CollatzResearch.WordTrace]
  refine ⟨174198349740045473247400127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116132233160030315498266751 174198349740045473247400127)
  ·
    refine ⟨261297524610068209871100191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174198349740045473247400127 261297524610068209871100191)
    ·
      refine ⟨391946286915102314806650287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261297524610068209871100191 391946286915102314806650287)
      ·
        refine ⟨587919430372653472209975431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 391946286915102314806650287 587919430372653472209975431)
        ·
          refine ⟨881879145558980208314963147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 587919430372653472209975431 881879145558980208314963147)
          ·
            refine ⟨1322818718338470312472444721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 881879145558980208314963147 1322818718338470312472444721)
            ·
              refine ⟨992114038753852734354333541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1322818718338470312472444721 992114038753852734354333541)
              ·
                refine ⟨186021382266347387691437539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 992114038753852734354333541 186021382266347387691437539)
                ·
                  refine ⟨279032073399521081537156309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 186021382266347387691437539 279032073399521081537156309)
                  ·
                    refine ⟨6539814220301275348527101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 279032073399521081537156309 6539814220301275348527101)
                    ·
                      refine ⟨2452430332612978255697663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6539814220301275348527101 2452430332612978255697663)
                      ·
                        rfl

theorem cell23_4776091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 7, 3].length) (baseStart_4776091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776091 prefixEnd_4776091 := by exact prefixLift 4776091
  have htrace : WordTrace (prefixWord ++ tailWord_4776091) baseStart_4776091 baseEnd_4776091 := by
    simpa [prefixWord, tailWord_4776091, baseEnd_4776091] using wordTrace_append hprefix tailTrace_4776091
  have hstable : (prefixWord ++ tailWord_4776091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776091).length < 2 ^ (prefixWord ++ tailWord_4776091).sum := by decide
  have hdescent : baseEnd_4776091 < baseStart_4776091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776095 : List Nat := [1, 1, 2, 6, 1, 1, 2, 2, 2, 2, 3]
def baseStart_4776095 : Nat := 118140960795 + 4776095 * 2 ^ 59
def prefixEnd_4776095 : Nat := 4983230072969 + 3 ^ 40 * 4776095 * 2
def baseEnd_4776095 : Nat := 2452432386535596240047645

theorem tailTrace_4776095 : CollatzResearch.WordTrace tailWord_4776095 prefixEnd_4776095 2452432386535596240047645 := by
  unfold tailWord_4776095
  simp only [CollatzResearch.WordTrace]
  refine ⟨174198495632030981930545739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116132330421353987953697159 174198495632030981930545739)
  ·
    refine ⟨261297743448046472895818609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174198495632030981930545739 261297743448046472895818609)
    ·
      refine ⟨195973307586034854671863957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261297743448046472895818609 195973307586034854671863957)
      ·
        refine ⟨9186248793095383812743623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 195973307586034854671863957 9186248793095383812743623)
        ·
          refine ⟨13779373189643075719115435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9186248793095383812743623 13779373189643075719115435)
          ·
            refine ⟨20669059784464613578673153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13779373189643075719115435 20669059784464613578673153)
            ·
              refine ⟨15501794838348460184004865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20669059784464613578673153 15501794838348460184004865)
              ·
                refine ⟨11626346128761345138003649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15501794838348460184004865 11626346128761345138003649)
                ·
                  refine ⟨8719759596571008853502737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11626346128761345138003649 8719759596571008853502737)
                  ·
                    refine ⟨6539819697428256640127053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8719759596571008853502737 6539819697428256640127053)
                    ·
                      refine ⟨2452432386535596240047645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6539819697428256640127053 2452432386535596240047645)
                      ·
                        rfl

theorem cell23_4776095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_4776095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776095 prefixEnd_4776095 := by exact prefixLift 4776095
  have htrace : WordTrace (prefixWord ++ tailWord_4776095) baseStart_4776095 baseEnd_4776095 := by
    simpa [prefixWord, tailWord_4776095, baseEnd_4776095] using wordTrace_append hprefix tailTrace_4776095
  have hstable : (prefixWord ++ tailWord_4776095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776095).length < 2 ^ (prefixWord ++ tailWord_4776095).sum := by decide
  have hdescent : baseEnd_4776095 < baseStart_4776095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776101 : List Nat := [1, 3, 1, 2, 1, 3, 2, 1, 1, 2, 6]
def baseStart_4776101 : Nat := 118140960795 + 4776101 * 2 ^ 59
def prefixEnd_4776101 : Nat := 4983230072969 + 3 ^ 40 * 4776101 * 2
def baseEnd_4776101 : Nat := 2452435467419523216572617

theorem tailTrace_4776101 : CollatzResearch.WordTrace tailWord_4776101 prefixEnd_4776101 2452435467419523216572617 := by
  unfold tailWord_4776101
  simp only [CollatzResearch.WordTrace]
  refine ⟨174198714470009244955264157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116132476313339496636842771 174198714470009244955264157)
  ·
    refine ⟨65324517926253466858224059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174198714470009244955264157 65324517926253466858224059)
    ·
      refine ⟨97986776889380200287336089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65324517926253466858224059 97986776889380200287336089)
      ·
        refine ⟨73490082667035150215502067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97986776889380200287336089 73490082667035150215502067)
        ·
          refine ⟨110235124000552725323253101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73490082667035150215502067 110235124000552725323253101)
          ·
            refine ⟨41338171500207271996219913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110235124000552725323253101 41338171500207271996219913)
            ·
              refine ⟨31003628625155453997164935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41338171500207271996219913 31003628625155453997164935)
              ·
                refine ⟨46505442937733180995747403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31003628625155453997164935 46505442937733180995747403)
                ·
                  refine ⟨69758164406599771493621105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46505442937733180995747403 69758164406599771493621105)
                  ·
                    refine ⟨52318623304949828620215829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 69758164406599771493621105 52318623304949828620215829)
                    ·
                      refine ⟨2452435467419523216572617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52318623304949828620215829 2452435467419523216572617)
                      ·
                        rfl

theorem cell23_4776101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_4776101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776101 prefixEnd_4776101 := by exact prefixLift 4776101
  have htrace : WordTrace (prefixWord ++ tailWord_4776101) baseStart_4776101 baseEnd_4776101 := by
    simpa [prefixWord, tailWord_4776101, baseEnd_4776101] using wordTrace_append hprefix tailTrace_4776101
  have hstable : (prefixWord ++ tailWord_4776101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776101).length < 2 ^ (prefixWord ++ tailWord_4776101).sum := by decide
  have hdescent : baseEnd_4776101 < baseStart_4776101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776121 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 2, 1, 7]
def baseStart_4776121 : Nat := 118140960795 + 4776121 * 2 ^ 59
def prefixEnd_4776121 : Nat := 4983230072969 + 3 ^ 40 * 4776121 * 2
def baseEnd_4776121 : Nat := 2452445737032613138322525

theorem tailTrace_4776121 : CollatzResearch.WordTrace tailWord_4776121 prefixEnd_4776121 2452445737032613138322525 := by
  unfold tailWord_4776121
  simp only [CollatzResearch.WordTrace]
  refine ⟨174199443929936788370992217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116132962619957858913994811 174199443929936788370992217)
  ·
    refine ⟨130649582947452591278244163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174199443929936788370992217 130649582947452591278244163)
    ·
      refine ⟨195974374421178886917366245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130649582947452591278244163 195974374421178886917366245)
      ·
        refine ⟨36745195203971041297006171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 195974374421178886917366245 36745195203971041297006171)
        ·
          refine ⟨55117792805956561945509257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36745195203971041297006171 55117792805956561945509257)
          ·
            refine ⟨41338344604467421459131943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55117792805956561945509257 41338344604467421459131943)
            ·
              refine ⟨62007516906701132188697915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41338344604467421459131943 62007516906701132188697915)
              ·
                refine ⟨93011275360051698283046873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62007516906701132188697915 93011275360051698283046873)
                ·
                  refine ⟨69758456520038773712285155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93011275360051698283046873 69758456520038773712285155)
                  ·
                    refine ⟨104637684780058160568427733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69758456520038773712285155 104637684780058160568427733)
                    ·
                      refine ⟨2452445737032613138322525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 104637684780058160568427733 2452445737032613138322525)
                      ·
                        rfl

theorem cell23_4776121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_4776121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776121 prefixEnd_4776121 := by exact prefixLift 4776121
  have htrace : WordTrace (prefixWord ++ tailWord_4776121) baseStart_4776121 baseEnd_4776121 := by
    simpa [prefixWord, tailWord_4776121, baseEnd_4776121] using wordTrace_append hprefix tailTrace_4776121
  have hstable : (prefixWord ++ tailWord_4776121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776121).length < 2 ^ (prefixWord ++ tailWord_4776121).sum := by decide
  have hdescent : baseEnd_4776121 < baseStart_4776121 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776128 : List Nat := [2, 1, 1, 2, 5, 1, 2, 1, 3, 5]
def baseStart_4776128 : Nat := 118140960795 + 4776128 * 2 ^ 59
def prefixEnd_4776128 : Nat := 4983230072969 + 3 ^ 40 * 4776128 * 2
def baseEnd_4776128 : Nat := 817483110465731536978331

theorem tailTrace_4776128 : CollatzResearch.WordTrace tailWord_4776128 prefixEnd_4776128 817483110465731536978331 := by
  unfold tailWord_4776128
  simp only [CollatzResearch.WordTrace]
  refine ⟨87099849620455714283248519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116133132827274285710998025 87099849620455714283248519)
  ·
    refine ⟨130649774430683571424872779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87099849620455714283248519 130649774430683571424872779)
    ·
      refine ⟨195974661646025357137309169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130649774430683571424872779 195974661646025357137309169)
      ·
        refine ⟨146980996234519017852981877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195974661646025357137309169 146980996234519017852981877)
        ·
          refine ⟨13779468396986157923717051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 146980996234519017852981877 13779468396986157923717051)
          ·
            refine ⟨20669202595479236885575577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13779468396986157923717051 20669202595479236885575577)
            ·
              refine ⟨15501901946609427664181683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20669202595479236885575577 15501901946609427664181683)
              ·
                refine ⟨23252852919914141496272525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15501901946609427664181683 23252852919914141496272525)
                ·
                  refine ⟨8719819844967803061102197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23252852919914141496272525 8719819844967803061102197)
                  ·
                    refine ⟨817483110465731536978331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8719819844967803061102197 817483110465731536978331)
                    ·
                      rfl

theorem cell23_4776128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 3, 5].length) (baseStart_4776128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776128 prefixEnd_4776128 := by exact prefixLift 4776128
  have htrace : WordTrace (prefixWord ++ tailWord_4776128) baseStart_4776128 baseEnd_4776128 := by
    simpa [prefixWord, tailWord_4776128, baseEnd_4776128] using wordTrace_append hprefix tailTrace_4776128
  have hstable : (prefixWord ++ tailWord_4776128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776128).length < 2 ^ (prefixWord ++ tailWord_4776128).sum := by decide
  have hdescent : baseEnd_4776128 < baseStart_4776128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776129 : List Nat := [1, 2, 6, 1, 2, 2, 1, 1, 2, 2, 3]
def baseStart_4776129 : Nat := 118140960795 + 4776129 * 2 ^ 59
def prefixEnd_4776129 : Nat := 4983230072969 + 3 ^ 40 * 4776129 * 2
def baseEnd_4776129 : Nat := 2452449844877849107022489

theorem tailTrace_4776129 : CollatzResearch.WordTrace tailWord_4776129 prefixEnd_4776129 2452449844877849107022489 := by
  unfold tailWord_4776129
  simp only [CollatzResearch.WordTrace]
  refine ⟨174199735713907805737283441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116133157142605203824855627 174199735713907805737283441)
  ·
    refine ⟨130649801785430854302962581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174199735713907805737283441 130649801785430854302962581)
    ·
      refine ⟨6124209458692071295451371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 130649801785430854302962581 6124209458692071295451371)
      ·
        refine ⟨9186314188038106943177057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6124209458692071295451371 9186314188038106943177057)
        ·
          refine ⟨6889735641028580207382793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9186314188038106943177057 6889735641028580207382793)
          ·
            refine ⟨5167301730771435155537095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6889735641028580207382793 5167301730771435155537095)
            ·
              refine ⟨7750952596157152733305643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5167301730771435155537095 7750952596157152733305643)
              ·
                refine ⟨11626428894235729099958465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7750952596157152733305643 11626428894235729099958465)
                ·
                  refine ⟨8719821670676796824968849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11626428894235729099958465 8719821670676796824968849)
                  ·
                    refine ⟨6539866253007597618726637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8719821670676796824968849 6539866253007597618726637)
                    ·
                      refine ⟨2452449844877849107022489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6539866253007597618726637 2452449844877849107022489)
                      ·
                        rfl

theorem cell23_4776129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_4776129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776129 prefixEnd_4776129 := by exact prefixLift 4776129
  have htrace : WordTrace (prefixWord ++ tailWord_4776129) baseStart_4776129 baseEnd_4776129 := by
    simpa [prefixWord, tailWord_4776129, baseEnd_4776129] using wordTrace_append hprefix tailTrace_4776129
  have hstable : (prefixWord ++ tailWord_4776129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776129).length < 2 ^ (prefixWord ++ tailWord_4776129).sum := by decide
  have hdescent : baseEnd_4776129 < baseStart_4776129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776145 : List Nat := [1, 2, 2, 1, 2, 2, 6, 1, 1, 5]
def baseStart_4776145 : Nat := 118140960795 + 4776145 * 2 ^ 59
def prefixEnd_4776145 : Nat := 4983230072969 + 3 ^ 40 * 4776145 * 2
def baseEnd_4776145 : Nat := 817486020189440348140805

theorem tailTrace_4776145 : CollatzResearch.WordTrace tailWord_4776145 prefixEnd_4776145 817486020189440348140805 := by
  unfold tailWord_4776145
  simp only [CollatzResearch.WordTrace]
  refine ⟨174200319281849840469865889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116133546187899893646577259 174200319281849840469865889)
  ·
    refine ⟨130650239461387380352399417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174200319281849840469865889 130650239461387380352399417)
    ·
      refine ⟨97987679596040535264299563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130650239461387380352399417 97987679596040535264299563)
      ·
        refine ⟨146981519394060802896449345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97987679596040535264299563 146981519394060802896449345)
        ·
          refine ⟨110236139545545602172337009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146981519394060802896449345 110236139545545602172337009)
          ·
            refine ⟨82677104659159201629252757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110236139545545602172337009 82677104659159201629252757)
            ·
              refine ⟨3875489280898087576371223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 82677104659159201629252757 3875489280898087576371223)
              ·
                refine ⟨5813233921347131364556835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3875489280898087576371223 5813233921347131364556835)
                ·
                  refine ⟨8719850882020697046835253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5813233921347131364556835 8719850882020697046835253)
                  ·
                    refine ⟨817486020189440348140805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8719850882020697046835253 817486020189440348140805)
                    ·
                      rfl

theorem cell23_4776145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 1, 1, 5].length) (baseStart_4776145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776145 prefixEnd_4776145 := by exact prefixLift 4776145
  have htrace : WordTrace (prefixWord ++ tailWord_4776145) baseStart_4776145 baseEnd_4776145 := by
    simpa [prefixWord, tailWord_4776145, baseEnd_4776145] using wordTrace_append hprefix tailTrace_4776145
  have hstable : (prefixWord ++ tailWord_4776145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776145).length < 2 ^ (prefixWord ++ tailWord_4776145).sum := by decide
  have hdescent : baseEnd_4776145 < baseStart_4776145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776168 : List Nat := [2, 1, 4, 1, 2, 2, 1, 1, 3, 1, 5]
def baseStart_4776168 : Nat := 118140960795 + 4776168 * 2 ^ 59
def prefixEnd_4776168 : Nat := 4983230072969 + 3 ^ 40 * 4776168 * 2
def baseEnd_4776168 : Nat := 2452469870623374454434809

theorem tailTrace_4776168 : CollatzResearch.WordTrace tailWord_4776168 prefixEnd_4776168 2452469870623374454434809 := by
  unfold tailWord_4776168
  simp only [CollatzResearch.WordTrace]
  refine ⟨87100579080383257698976579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116134105440511010265302105 87100579080383257698976579)
  ·
    refine ⟨130650868620574886548464869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87100579080383257698976579 130650868620574886548464869)
    ·
      refine ⟨24497037866357791227837163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130650868620574886548464869 24497037866357791227837163)
      ·
        refine ⟨36745556799536686841755745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24497037866357791227837163 36745556799536686841755745)
        ·
          refine ⟨27559167599652515131316809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36745556799536686841755745 27559167599652515131316809)
          ·
            refine ⟨20669375699739386348487607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27559167599652515131316809 20669375699739386348487607)
            ·
              refine ⟨31004063549609079522731411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20669375699739386348487607 31004063549609079522731411)
              ·
                refine ⟨46506095324413619284097117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31004063549609079522731411 46506095324413619284097117)
                ·
                  refine ⟨17439785746655107231536419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46506095324413619284097117 17439785746655107231536419)
                  ·
                    refine ⟨26159678619982660847304629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17439785746655107231536419 26159678619982660847304629)
                    ·
                      refine ⟨2452469870623374454434809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26159678619982660847304629 2452469870623374454434809)
                      ·
                        rfl

theorem cell23_4776168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_4776168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776168 prefixEnd_4776168 := by exact prefixLift 4776168
  have htrace : WordTrace (prefixWord ++ tailWord_4776168) baseStart_4776168 baseEnd_4776168 := by
    simpa [prefixWord, tailWord_4776168, baseEnd_4776168] using wordTrace_append hprefix tailTrace_4776168
  have hstable : (prefixWord ++ tailWord_4776168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776168).length < 2 ^ (prefixWord ++ tailWord_4776168).sum := by decide
  have hdescent : baseEnd_4776168 < baseStart_4776168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776171 : List Nat := [1, 1, 1, 1, 2, 5, 2, 10]
def baseStart_4776171 : Nat := 118140960795 + 4776171 * 2 ^ 59
def prefixEnd_4776171 : Nat := 4983230072969 + 3 ^ 40 * 4776171 * 2
def baseEnd_4776171 : Nat := 90832274483901405285085

theorem tailTrace_4776171 : CollatzResearch.WordTrace tailWord_4776171 prefixEnd_4776171 90832274483901405285085 := by
  unfold tailWord_4776171
  simp only [CollatzResearch.WordTrace]
  refine ⟨174201267579755646910312367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116134178386503764606874911 174201267579755646910312367)
  ·
    refine ⟨261301901369633470365468551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174201267579755646910312367 261301901369633470365468551)
    ·
      refine ⟨391952852054450205548202827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261301901369633470365468551 391952852054450205548202827)
      ·
        refine ⟨587929278081675308322304241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 391952852054450205548202827 587929278081675308322304241)
        ·
          refine ⟨440946958561256481241728181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 587929278081675308322304241 440946958561256481241728181)
          ·
            refine ⟨41338777365117795116412017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 440946958561256481241728181 41338777365117795116412017)
            ·
              refine ⟨31004083023838346337309013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41338777365117795116412017 31004083023838346337309013)
              ·
                refine ⟨90832274483901405285085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 31004083023838346337309013 90832274483901405285085)
                ·
                  rfl

theorem cell23_4776171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 10].length) (baseStart_4776171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776171 prefixEnd_4776171 := by exact prefixLift 4776171
  have htrace : WordTrace (prefixWord ++ tailWord_4776171) baseStart_4776171 baseEnd_4776171 := by
    simpa [prefixWord, tailWord_4776171, baseEnd_4776171] using wordTrace_append hprefix tailTrace_4776171
  have hstable : (prefixWord ++ tailWord_4776171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776171).length < 2 ^ (prefixWord ++ tailWord_4776171).sum := by decide
  have hdescent : baseEnd_4776171 < baseStart_4776171 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776175 : List Nat := [1, 1, 2, 1, 6, 3, 1, 1, 1, 6]
def baseStart_4776175 : Nat := 118140960795 + 4776175 * 2 ^ 59
def prefixEnd_4776175 : Nat := 4983230072969 + 3 ^ 40 * 4776175 * 2
def baseEnd_4776175 : Nat := 817491154995985309015759

theorem tailTrace_4776175 : CollatzResearch.WordTrace tailWord_4776175 prefixEnd_4776175 817491154995985309015759 := by
  unfold tailWord_4776175
  simp only [CollatzResearch.WordTrace]
  refine ⟨174201413471741155593457979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116134275647827437062305319 174201413471741155593457979)
  ·
    refine ⟨261302120207611733390186969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174201413471741155593457979 261302120207611733390186969)
    ·
      refine ⟨195976590155708800042640227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261302120207611733390186969 195976590155708800042640227)
      ·
        refine ⟨293964885233563200063960341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195976590155708800042640227 293964885233563200063960341)
        ·
          refine ⟨13779603995323275002998141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 293964885233563200063960341 13779603995323275002998141)
          ·
            refine ⟨5167351498246228126124303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13779603995323275002998141 5167351498246228126124303)
            ·
              refine ⟨7751027247369342189186455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5167351498246228126124303 7751027247369342189186455)
              ·
                refine ⟨11626540871054013283779683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7751027247369342189186455 11626540871054013283779683)
                ·
                  refine ⟨17439811306581019925669525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11626540871054013283779683 17439811306581019925669525)
                  ·
                    refine ⟨817491154995985309015759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17439811306581019925669525 817491154995985309015759)
                    ·
                      rfl

theorem cell23_4776175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 6].length) (baseStart_4776175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776175 prefixEnd_4776175 := by exact prefixLift 4776175
  have htrace : WordTrace (prefixWord ++ tailWord_4776175) baseStart_4776175 baseEnd_4776175 := by
    simpa [prefixWord, tailWord_4776175, baseEnd_4776175] using wordTrace_append hprefix tailTrace_4776175
  have hstable : (prefixWord ++ tailWord_4776175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776175).length < 2 ^ (prefixWord ++ tailWord_4776175).sum := by decide
  have hdescent : baseEnd_4776175 < baseStart_4776175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776188 : List Nat := [2, 2, 2, 1, 4, 2, 1, 9]
def baseStart_4776188 : Nat := 118140960795 + 4776188 * 2 ^ 59
def prefixEnd_4776188 : Nat := 4983230072969 + 3 ^ 40 * 4776188 * 2
def baseEnd_4776188 : Nat := 90832597786535717636471

theorem tailTrace_4776188 : CollatzResearch.WordTrace tailWord_4776188 prefixEnd_4776188 90832597786535717636471 := by
  unfold tailWord_4776188
  simp only [CollatzResearch.WordTrace]
  refine ⟨87100943810347029406840609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116134591747129372542454145 87100943810347029406840609)
  ·
    refine ⟨65325707857760272055130457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87100943810347029406840609 65325707857760272055130457)
    ·
      refine ⟨48994280893320204041347843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65325707857760272055130457 48994280893320204041347843)
      ·
        refine ⟨73491421339980306062021765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48994280893320204041347843 73491421339980306062021765)
        ·
          refine ⟨13779641501246307386629081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73491421339980306062021765 13779641501246307386629081)
          ·
            refine ⟨10334731125934730539971811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13779641501246307386629081 10334731125934730539971811)
            ·
              refine ⟨15502096688902095809957717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10334731125934730539971811 15502096688902095809957717)
              ·
                refine ⟨90832597786535717636471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15502096688902095809957717 90832597786535717636471)
                ·
                  rfl

theorem cell23_4776188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 9].length) (baseStart_4776188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776188 prefixEnd_4776188 := by exact prefixLift 4776188
  have htrace : WordTrace (prefixWord ++ tailWord_4776188) baseStart_4776188 baseEnd_4776188 := by
    simpa [prefixWord, tailWord_4776188, baseEnd_4776188] using wordTrace_append hprefix tailTrace_4776188
  have hstable : (prefixWord ++ tailWord_4776188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776188).length < 2 ^ (prefixWord ++ tailWord_4776188).sum := by decide
  have hdescent : baseEnd_4776188 < baseStart_4776188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776216 : List Nat := [2, 1, 2, 3, 1, 2, 5, 2, 1, 2, 2]
def baseStart_4776216 : Nat := 118140960795 + 4776216 * 2 ^ 59
def prefixEnd_4776216 : Nat := 4983230072969 + 3 ^ 40 * 4776216 * 2
def baseEnd_4776216 : Nat := 2452494517694790266634589

theorem tailTrace_4776216 : CollatzResearch.WordTrace tailWord_4776216 prefixEnd_4776216 2452494517694790266634589 := by
  unfold tailWord_4776216
  simp only [CollatzResearch.WordTrace]
  refine ⟨87101454432296309797850251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116135272576395079730467001 87101454432296309797850251)
  ·
    refine ⟨130652181648444464696775377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87101454432296309797850251 130652181648444464696775377)
    ·
      refine ⟨97989136236333348522581533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130652181648444464696775377 97989136236333348522581533)
      ·
        refine ⟨36745926088625005695968075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97989136236333348522581533 36745926088625005695968075)
        ·
          refine ⟨55118889132937508543952113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36745926088625005695968075 55118889132937508543952113)
          ·
            refine ⟨41339166849703131407964085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55118889132937508543952113 41339166849703131407964085)
            ·
              refine ⟨3875546892159668569496633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41339166849703131407964085 3875546892159668569496633)
              ·
                refine ⟨2906660169119751427122475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3875546892159668569496633 2906660169119751427122475)
                ·
                  refine ⟨4359990253679627140683713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2906660169119751427122475 4359990253679627140683713)
                  ·
                    refine ⟨3269992690259720355512785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4359990253679627140683713 3269992690259720355512785)
                    ·
                      refine ⟨2452494517694790266634589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3269992690259720355512785 2452494517694790266634589)
                      ·
                        rfl

theorem cell23_4776216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 2, 1, 2, 2].length) (baseStart_4776216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776216 prefixEnd_4776216 := by exact prefixLift 4776216
  have htrace : WordTrace (prefixWord ++ tailWord_4776216) baseStart_4776216 baseEnd_4776216 := by
    simpa [prefixWord, tailWord_4776216, baseEnd_4776216] using wordTrace_append hprefix tailTrace_4776216
  have hstable : (prefixWord ++ tailWord_4776216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776216).length < 2 ^ (prefixWord ++ tailWord_4776216).sum := by decide
  have hdescent : baseEnd_4776216 < baseStart_4776216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776222 : List Nat := [4, 3, 2, 1, 1, 2, 2, 8]
def baseStart_4776222 : Nat := 118140960795 + 4776222 * 2 ^ 59
def prefixEnd_4776222 : Nat := 4983230072969 + 3 ^ 40 * 4776222 * 2
def baseEnd_4776222 : Nat := 90833244391804342339243

theorem tailTrace_4776222 : CollatzResearch.WordTrace tailWord_4776222 prefixEnd_4776222 90833244391804342339243 := by
  unfold tailWord_4776222
  simp only [CollatzResearch.WordTrace]
  refine ⟨21775390962821360327552365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116135418468380588413612613 21775390962821360327552365)
  ·
    refine ⟨8165771611058010122832137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21775390962821360327552365 8165771611058010122832137)
    ·
      refine ⟨6124328708293507592124103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8165771611058010122832137 6124328708293507592124103)
      ·
        refine ⟨9186493062440261388186155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6124328708293507592124103 9186493062440261388186155)
        ·
          refine ⟨13779739593660392082279233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9186493062440261388186155 13779739593660392082279233)
          ·
            refine ⟨10334804695245294061709425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13779739593660392082279233 10334804695245294061709425)
            ·
              refine ⟨7751103521433970546282069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10334804695245294061709425 7751103521433970546282069)
              ·
                refine ⟨90833244391804342339243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7751103521433970546282069 90833244391804342339243)
                ·
                  rfl

theorem cell23_4776222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 8].length) (baseStart_4776222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776222 prefixEnd_4776222 := by exact prefixLift 4776222
  have htrace : WordTrace (prefixWord ++ tailWord_4776222) baseStart_4776222 baseEnd_4776222 := by
    simpa [prefixWord, tailWord_4776222, baseEnd_4776222] using wordTrace_append hprefix tailTrace_4776222
  have hstable : (prefixWord ++ tailWord_4776222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776222).length < 2 ^ (prefixWord ++ tailWord_4776222).sum := by decide
  have hdescent : baseEnd_4776222 < baseStart_4776222 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776295 : List Nat := [1, 1, 5, 1, 3, 2, 1, 2, 7]
def baseStart_4776295 : Nat := 118140960795 + 4776295 * 2 ^ 59
def prefixEnd_4776295 : Nat := 4983230072969 + 3 ^ 40 * 4776295 * 2
def baseEnd_4776295 : Nat := 272503898074055050838525

theorem tailTrace_4776295 : CollatzResearch.WordTrace tailWord_4776295 prefixEnd_4776295 272503898074055050838525 := by
  unfold tailWord_4776295
  simp only [CollatzResearch.WordTrace]
  refine ⟨174205790231306416087826339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116137193487537610725217559 174205790231306416087826339)
  ·
    refine ⟨261308685346959624131739509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174205790231306416087826339 261308685346959624131739509)
    ·
      refine ⟨24497689251277464762350579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 261308685346959624131739509 24497689251277464762350579)
      ·
        refine ⟨36746533876916197143525869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24497689251277464762350579 36746533876916197143525869)
        ·
          refine ⟨13779950203843573928822201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36746533876916197143525869 13779950203843573928822201)
          ·
            refine ⟨10334962652882680446616651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13779950203843573928822201 10334962652882680446616651)
            ·
              refine ⟨15502443979324020669924977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10334962652882680446616651 15502443979324020669924977)
              ·
                refine ⟨11626832984493015502443733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15502443979324020669924977 11626832984493015502443733)
                ·
                  refine ⟨272503898074055050838525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11626832984493015502443733 272503898074055050838525)
                  ·
                    rfl

theorem cell23_4776295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 7].length) (baseStart_4776295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776295 prefixEnd_4776295 := by exact prefixLift 4776295
  have htrace : WordTrace (prefixWord ++ tailWord_4776295) baseStart_4776295 baseEnd_4776295 := by
    simpa [prefixWord, tailWord_4776295, baseEnd_4776295] using wordTrace_append hprefix tailTrace_4776295
  have hstable : (prefixWord ++ tailWord_4776295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776295).length < 2 ^ (prefixWord ++ tailWord_4776295).sum := by decide
  have hdescent : baseEnd_4776295 < baseStart_4776295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776310 : List Nat := [5, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2]
def baseStart_4776310 : Nat := 118140960795 + 4776310 * 2 ^ 59
def prefixEnd_4776310 : Nat := 4983230072969 + 3 ^ 40 * 4776310 * 2
def baseEnd_4776310 : Nat := 2452542784876312898859157

theorem tailTrace_4776310 : CollatzResearch.WordTrace tailWord_4776310 prefixEnd_4776310 2452542784876312898859157 := by
  unfold tailWord_4776310
  simp only [CollatzResearch.WordTrace]
  refine ⟨10887896082890754603101399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116137558217501382433081589 10887896082890754603101399)
  ·
    refine ⟨16331844124336131904652099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10887896082890754603101399 16331844124336131904652099)
    ·
      refine ⟨24497766186504197856978149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16331844124336131904652099 24497766186504197856978149)
      ·
        refine ⟨4593331159969537098183403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24497766186504197856978149 4593331159969537098183403)
        ·
          refine ⟨6889996739954305647275105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4593331159969537098183403 6889996739954305647275105)
          ·
            refine ⟨5167497554965729235456329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6889996739954305647275105 5167497554965729235456329)
            ·
              refine ⟨3875623166224296926592247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5167497554965729235456329 3875623166224296926592247)
              ·
                refine ⟨5813434749336445389888371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3875623166224296926592247 5813434749336445389888371)
                ·
                  refine ⟨8720152124004668084832557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5813434749336445389888371 8720152124004668084832557)
                  ·
                    refine ⟨3270057046501750531812209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8720152124004668084832557 3270057046501750531812209)
                    ·
                      refine ⟨2452542784876312898859157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3270057046501750531812209 2452542784876312898859157)
                      ·
                        rfl

theorem cell23_4776310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_4776310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776310 prefixEnd_4776310 := by exact prefixLift 4776310
  have htrace : WordTrace (prefixWord ++ tailWord_4776310) baseStart_4776310 baseEnd_4776310 := by
    simpa [prefixWord, tailWord_4776310, baseEnd_4776310] using wordTrace_append hprefix tailTrace_4776310
  have hstable : (prefixWord ++ tailWord_4776310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776310).length < 2 ^ (prefixWord ++ tailWord_4776310).sum := by decide
  have hdescent : baseEnd_4776310 < baseStart_4776310 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776323 : List Nat := [1, 1, 1, 3, 7, 1, 1, 2, 2, 2, 2]
def baseStart_4776323 : Nat := 118140960795 + 4776323 * 2 ^ 59
def prefixEnd_4776323 : Nat := 4983230072969 + 3 ^ 40 * 4776323 * 2
def baseEnd_4776323 : Nat := 2452549460124821347996597

theorem tailTrace_4776323 : CollatzResearch.WordTrace tailWord_4776323 prefixEnd_4776323 2452549460124821347996597 := by
  unfold tailWord_4776323
  simp only [CollatzResearch.WordTrace]
  refine ⟨174206811475204976869845623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116137874316803317913230415 174206811475204976869845623)
  ·
    refine ⟨261310217212807465304768435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174206811475204976869845623 261310217212807465304768435)
    ·
      refine ⟨391965325819211197957152653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261310217212807465304768435 391965325819211197957152653)
      ·
        refine ⟨146986997182204199233932245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 391965325819211197957152653 146986997182204199233932245)
        ·
          refine ⟨3445007746457910919545287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 146986997182204199233932245 3445007746457910919545287)
          ·
            refine ⟨5167511619686866379317931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3445007746457910919545287 5167511619686866379317931)
            ·
              refine ⟨7751267429530299568976897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5167511619686866379317931 7751267429530299568976897)
              ·
                refine ⟨5813450572147724676732673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7751267429530299568976897 5813450572147724676732673)
                ·
                  refine ⟨4360087929110793507549505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5813450572147724676732673 4360087929110793507549505)
                  ·
                    refine ⟨3270065946833095130662129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4360087929110793507549505 3270065946833095130662129)
                    ·
                      refine ⟨2452549460124821347996597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3270065946833095130662129 2452549460124821347996597)
                      ·
                        rfl

theorem cell23_4776323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 2, 2, 2, 2].length) (baseStart_4776323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776323 prefixEnd_4776323 := by exact prefixLift 4776323
  have htrace : WordTrace (prefixWord ++ tailWord_4776323) baseStart_4776323 baseEnd_4776323 := by
    simpa [prefixWord, tailWord_4776323, baseEnd_4776323] using wordTrace_append hprefix tailTrace_4776323
  have hstable : (prefixWord ++ tailWord_4776323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776323).length < 2 ^ (prefixWord ++ tailWord_4776323).sum := by decide
  have hdescent : baseEnd_4776323 < baseStart_4776323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776382 : List Nat := [4, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3]
def baseStart_4776382 : Nat := 118140960795 + 4776382 * 2 ^ 59
def prefixEnd_4776382 : Nat := 4983230072969 + 3 ^ 40 * 4776382 * 2
def baseEnd_4776382 : Nat := 2452579755483436617158825

theorem tailTrace_4776382 : CollatzResearch.WordTrace tailWord_4776382 prefixEnd_4776382 2452579755483436617158825 := by
  unfold tailWord_4776382
  simp only [CollatzResearch.WordTrace]
  refine ⟨21776120422748903743280425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116139308921327486630828933 21776120422748903743280425)
  ·
    refine ⟨16332090317061677807460319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21776120422748903743280425 16332090317061677807460319)
    ·
      refine ⟨24498135475592516711190479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16332090317061677807460319 24498135475592516711190479)
      ·
        refine ⟨36747203213388775066785719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24498135475592516711190479 36747203213388775066785719)
        ·
          refine ⟨55120804820083162600178579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36747203213388775066785719 55120804820083162600178579)
          ·
            refine ⟨82681207230124743900267869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55120804820083162600178579 82681207230124743900267869)
            ·
              refine ⟨31005452711296778962600451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82681207230124743900267869 31005452711296778962600451)
              ·
                refine ⟨46508179066945168443900677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31005452711296778962600451 46508179066945168443900677)
                ·
                  refine ⟨8720283575052219083231377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46508179066945168443900677 8720283575052219083231377)
                  ·
                    refine ⟨6540212681289164312423533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8720283575052219083231377 6540212681289164312423533)
                    ·
                      refine ⟨2452579755483436617158825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6540212681289164312423533 2452579755483436617158825)
                      ·
                        rfl

theorem cell23_4776382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_4776382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776382 prefixEnd_4776382 := by exact prefixLift 4776382
  have htrace : WordTrace (prefixWord ++ tailWord_4776382) baseStart_4776382 baseEnd_4776382 := by
    simpa [prefixWord, tailWord_4776382, baseEnd_4776382] using wordTrace_append hprefix tailTrace_4776382
  have hstable : (prefixWord ++ tailWord_4776382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776382).length < 2 ^ (prefixWord ++ tailWord_4776382).sum := by decide
  have hdescent : baseEnd_4776382 < baseStart_4776382 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776445 : List Nat := [1, 4, 1, 1, 1, 3, 1, 2, 3, 6]
def baseStart_4776445 : Nat := 118140960795 + 4776445 * 2 ^ 59
def prefixEnd_4776445 : Nat := 4983230072969 + 3 ^ 40 * 4776445 * 2
def baseEnd_4776445 : Nat := 817537368254889956890345

theorem tailTrace_4776445 : CollatzResearch.WordTrace tailWord_4776445 prefixEnd_4776445 817537368254889956890345 := by
  unfold tailWord_4776445
  simp only [CollatzResearch.WordTrace]
  refine ⟨174211261180762991705786789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116140840787175327803857859 174211261180762991705786789)
  ·
    refine ⟨32664611471393060944835023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174211261180762991705786789 32664611471393060944835023)
    ·
      refine ⟨48996917207089591417252535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32664611471393060944835023 48996917207089591417252535)
      ·
        refine ⟨73495375810634387125878803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48996917207089591417252535 73495375810634387125878803)
        ·
          refine ⟨110243063715951580688818205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73495375810634387125878803 110243063715951580688818205)
          ·
            refine ⟨41341148893481842758306827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110243063715951580688818205 41341148893481842758306827)
            ·
              refine ⟨62011723340222764137460241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41341148893481842758306827 62011723340222764137460241)
              ·
                refine ⟨46508792505167073103095181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62011723340222764137460241 46508792505167073103095181)
                ·
                  refine ⟨17440797189437652413660693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46508792505167073103095181 17440797189437652413660693)
                  ·
                    refine ⟨817537368254889956890345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17440797189437652413660693 817537368254889956890345)
                    ·
                      rfl

theorem cell23_4776445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_4776445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776445 prefixEnd_4776445 := by exact prefixLift 4776445
  have htrace : WordTrace (prefixWord ++ tailWord_4776445) baseStart_4776445 baseEnd_4776445 := by
    simpa [prefixWord, tailWord_4776445, baseEnd_4776445] using wordTrace_append hprefix tailTrace_4776445
  have hstable : (prefixWord ++ tailWord_4776445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776445).length < 2 ^ (prefixWord ++ tailWord_4776445).sum := by decide
  have hdescent : baseEnd_4776445 < baseStart_4776445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776462 : List Nat := [4, 1, 1, 2, 3, 1, 1, 3, 1, 6]
def baseStart_4776462 : Nat := 118140960795 + 4776462 * 2 ^ 59
def prefixEnd_4776462 : Nat := 4983230072969 + 3 ^ 40 * 4776462 * 2
def baseEnd_4776462 : Nat := 817540277978598768052819

theorem tailTrace_4776462 : CollatzResearch.WordTrace tailWord_4776462 prefixEnd_4776462 817540277978598768052819 := by
  unfold tailWord_4776462
  simp only [CollatzResearch.WordTrace]
  refine ⟨21776485152712675451144455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116141254147800935739437093 21776485152712675451144455)
  ·
    refine ⟨32664727729069013176716683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21776485152712675451144455 32664727729069013176716683)
    ·
      refine ⟨48997091593603519765075025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32664727729069013176716683 48997091593603519765075025)
      ·
        refine ⟨36747818695202639823806269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48997091593603519765075025 36747818695202639823806269)
        ·
          refine ⟨13780432010700989933927351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36747818695202639823806269 13780432010700989933927351)
          ·
            refine ⟨20670648016051484900891027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13780432010700989933927351 20670648016051484900891027)
            ·
              refine ⟨31005972024077227351336541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20670648016051484900891027 31005972024077227351336541)
              ·
                refine ⟨11627239509028960256751203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31005972024077227351336541 11627239509028960256751203)
                ·
                  refine ⟨17440859263543440385126805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11627239509028960256751203 17440859263543440385126805)
                  ·
                    refine ⟨817540277978598768052819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17440859263543440385126805 817540277978598768052819)
                    ·
                      rfl

theorem cell23_4776462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_4776462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776462 prefixEnd_4776462 := by exact prefixLift 4776462
  have htrace : WordTrace (prefixWord ++ tailWord_4776462) baseStart_4776462 baseEnd_4776462 := by
    simpa [prefixWord, tailWord_4776462, baseEnd_4776462] using wordTrace_append hprefix tailTrace_4776462
  have hstable : (prefixWord ++ tailWord_4776462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776462).length < 2 ^ (prefixWord ++ tailWord_4776462).sum := by decide
  have hdescent : baseEnd_4776462 < baseStart_4776462 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776515 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 5]
def baseStart_4776515 : Nat := 118140960795 + 4776515 * 2 ^ 59
def prefixEnd_4776515 : Nat := 4983230072969 + 3 ^ 40 * 4776515 * 2
def baseEnd_4776515 : Nat := 2452648048410484596795713

theorem tailTrace_4776515 : CollatzResearch.WordTrace tailWord_4776515 prefixEnd_4776515 2452648048410484596795713 := by
  unfold tailWord_4776515
  simp only [CollatzResearch.WordTrace]
  refine ⟨174213814290509393660834999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116142542860339595773889999 174213814290509393660834999)
  ·
    refine ⟨261320721435764090491252499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174213814290509393660834999 261320721435764090491252499)
    ·
      refine ⟨391981082153646135736878749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261320721435764090491252499 391981082153646135736878749)
      ·
        refine ⟨146992905807617300901329531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 391981082153646135736878749 146992905807617300901329531)
        ·
          refine ⟨220489358711425951351994297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146992905807617300901329531 220489358711425951351994297)
          ·
            refine ⟨165367019033569463513995723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220489358711425951351994297 165367019033569463513995723)
            ·
              refine ⟨248050528550354195270993585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165367019033569463513995723 248050528550354195270993585)
              ·
                refine ⟨186037896412765646453245189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 248050528550354195270993585 186037896412765646453245189)
                ·
                  refine ⟨34882105577393558709983473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 186037896412765646453245189 34882105577393558709983473)
                  ·
                    refine ⟨26161579183045169032487605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34882105577393558709983473 26161579183045169032487605)
                    ·
                      refine ⟨2452648048410484596795713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26161579183045169032487605 2452648048410484596795713)
                      ·
                        rfl

theorem cell23_4776515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_4776515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776515 prefixEnd_4776515 := by exact prefixLift 4776515
  have htrace : WordTrace (prefixWord ++ tailWord_4776515) baseStart_4776515 baseEnd_4776515 := by
    simpa [prefixWord, tailWord_4776515, baseEnd_4776515] using wordTrace_append hprefix tailTrace_4776515
  have hstable : (prefixWord ++ tailWord_4776515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776515).length < 2 ^ (prefixWord ++ tailWord_4776515).sum := by decide
  have hdescent : baseEnd_4776515 < baseStart_4776515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776519 : List Nat := [1, 1, 4, 1, 4, 1, 3, 1, 1, 3, 3]
def baseStart_4776519 : Nat := 118140960795 + 4776519 * 2 ^ 59
def prefixEnd_4776519 : Nat := 4983230072969 + 3 ^ 40 * 4776519 * 2
def baseEnd_4776519 : Nat := 2452650102333102581145695

theorem tailTrace_4776519 : CollatzResearch.WordTrace tailWord_4776519 prefixEnd_4776519 2452650102333102581145695 := by
  unfold tailWord_4776519
  simp only [CollatzResearch.WordTrace]
  refine ⟨174213960182494902343980611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116142640121663268229320407 174213960182494902343980611)
  ·
    refine ⟨261320940273742353515970917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174213960182494902343980611 261320940273742353515970917)
    ·
      refine ⟨48997676301326691284244547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 261320940273742353515970917 48997676301326691284244547)
      ·
        refine ⟨73496514451990036926366821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48997676301326691284244547 73496514451990036926366821)
        ·
          refine ⟨13780596459748131923693779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73496514451990036926366821 13780596459748131923693779)
          ·
            refine ⟨20670894689622197885540669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13780596459748131923693779 20670894689622197885540669)
            ·
              refine ⟨7751585508608324207077751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20670894689622197885540669 7751585508608324207077751)
              ·
                refine ⟨11627378262912486310616627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7751585508608324207077751 11627378262912486310616627)
                ·
                  refine ⟨17441067394368729465924941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11627378262912486310616627 17441067394368729465924941)
                  ·
                    refine ⟨6540400272888273549721853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17441067394368729465924941 6540400272888273549721853)
                    ·
                      refine ⟨2452650102333102581145695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6540400272888273549721853 2452650102333102581145695)
                      ·
                        rfl

theorem cell23_4776519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 3, 3].length) (baseStart_4776519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776519 prefixEnd_4776519 := by exact prefixLift 4776519
  have htrace : WordTrace (prefixWord ++ tailWord_4776519) baseStart_4776519 baseEnd_4776519 := by
    simpa [prefixWord, tailWord_4776519, baseEnd_4776519] using wordTrace_append hprefix tailTrace_4776519
  have hstable : (prefixWord ++ tailWord_4776519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776519).length < 2 ^ (prefixWord ++ tailWord_4776519).sum := by decide
  have hdescent : baseEnd_4776519 < baseStart_4776519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776532 : List Nat := [2, 4, 1, 1, 1, 3, 1, 1, 2, 2, 5]
def baseStart_4776532 : Nat := 118140960795 + 4776532 * 2 ^ 59
def prefixEnd_4776532 : Nat := 4983230072969 + 3 ^ 40 * 4776532 * 2
def baseEnd_4776532 : Nat := 2452656777581611030283135

theorem tailTrace_4776532 : CollatzResearch.WordTrace tailWord_4776532 prefixEnd_4776532 2452656777581611030283135 := by
  unfold tailWord_4776532
  simp only [CollatzResearch.WordTrace]
  refine ⟨87107217165723902782101925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116142956220965203709469233 87107217165723902782101925)
  ·
    refine ⟨16332603218573231771644111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87107217165723902782101925 16332603218573231771644111)
    ·
      refine ⟨24498904827859847657466167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16332603218573231771644111 24498904827859847657466167)
      ·
        refine ⟨36748357241789771486199251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24498904827859847657466167 36748357241789771486199251)
        ·
          refine ⟨55122535862684657229298877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36748357241789771486199251 55122535862684657229298877)
          ·
            refine ⟨20670950948506746460987079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55122535862684657229298877 20670950948506746460987079)
            ·
              refine ⟨31006426422760119691480619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20670950948506746460987079 31006426422760119691480619)
              ·
                refine ⟨46509639634140179537220929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31006426422760119691480619 46509639634140179537220929)
                ·
                  refine ⟨34882229725605134652915697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46509639634140179537220929 34882229725605134652915697)
                  ·
                    refine ⟨26161672294203850989686773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34882229725605134652915697 26161672294203850989686773)
                    ·
                      refine ⟨2452656777581611030283135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26161672294203850989686773 2452656777581611030283135)
                      ·
                        rfl

theorem cell23_4776532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_4776532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776532 prefixEnd_4776532 := by exact prefixLift 4776532
  have htrace : WordTrace (prefixWord ++ tailWord_4776532) baseStart_4776532 baseEnd_4776532 := by
    simpa [prefixWord, tailWord_4776532, baseEnd_4776532] using wordTrace_append hprefix tailTrace_4776532
  have hstable : (prefixWord ++ tailWord_4776532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776532).length < 2 ^ (prefixWord ++ tailWord_4776532).sum := by decide
  have hdescent : baseEnd_4776532 < baseStart_4776532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776555 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 6]
def baseStart_4776555 : Nat := 118140960795 + 4776555 * 2 ^ 59
def prefixEnd_4776555 : Nat := 4983230072969 + 3 ^ 40 * 4776555 * 2
def baseEnd_4776555 : Nat := 2452668587636664440295529

theorem tailTrace_4776555 : CollatzResearch.WordTrace tailWord_4776555 prefixEnd_4776555 2452668587636664440295529 := by
  unfold tailWord_4776555
  simp only [CollatzResearch.WordTrace]
  refine ⟨174215273210364480492291119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116143515473576320328194079 174215273210364480492291119)
  ·
    refine ⟨261322909815546720738436679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174215273210364480492291119 261322909815546720738436679)
    ·
      refine ⟨391984364723320081107655019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261322909815546720738436679 391984364723320081107655019)
      ·
        refine ⟨587976547084980121661482529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 391984364723320081107655019 587976547084980121661482529)
        ·
          refine ⟨440982410313735091246111897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 587976547084980121661482529 440982410313735091246111897)
          ·
            refine ⟨330736807735301318434583923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 440982410313735091246111897 330736807735301318434583923)
            ·
              refine ⟨496105211602951977651875885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 330736807735301318434583923 496105211602951977651875885)
              ·
                refine ⟨186039454351106991619453457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 496105211602951977651875885 186039454351106991619453457)
                ·
                  refine ⟨139529590763330243714590093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 186039454351106991619453457 139529590763330243714590093)
                  ·
                    refine ⟨52323596536248841392971285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 139529590763330243714590093 52323596536248841392971285)
                    ·
                      refine ⟨2452668587636664440295529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52323596536248841392971285 2452668587636664440295529)
                      ·
                        rfl

theorem cell23_4776555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 6].length) (baseStart_4776555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776555 prefixEnd_4776555 := by exact prefixLift 4776555
  have htrace : WordTrace (prefixWord ++ tailWord_4776555) baseStart_4776555 baseEnd_4776555 := by
    simpa [prefixWord, tailWord_4776555, baseEnd_4776555] using wordTrace_append hprefix tailTrace_4776555
  have hstable : (prefixWord ++ tailWord_4776555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776555).length < 2 ^ (prefixWord ++ tailWord_4776555).sum := by decide
  have hdescent : baseEnd_4776555 < baseStart_4776555 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776572 : List Nat := [2, 2, 2, 1, 1, 2, 2, 3, 2, 2, 4]
def baseStart_4776572 : Nat := 118140960795 + 4776572 * 2 ^ 59
def prefixEnd_4776572 : Nat := 4983230072969 + 3 ^ 40 * 4776572 * 2
def baseEnd_4776572 : Nat := 2452677316807790873782951

theorem tailTrace_4776572 : CollatzResearch.WordTrace tailWord_4776572 prefixEnd_4776572 2452677316807790873782951 := by
  unfold tailWord_4776572
  simp only [CollatzResearch.WordTrace]
  refine ⟨87107946625651446197829985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116143928834201928263773313 87107946625651446197829985)
  ·
    refine ⟨65330959969238584648372489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87107946625651446197829985 65330959969238584648372489)
    ·
      refine ⟨48998219976928938486279367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65330959969238584648372489 48998219976928938486279367)
      ·
        refine ⟨73497329965393407729419051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48998219976928938486279367 73497329965393407729419051)
        ·
          refine ⟨110245994948090111594128577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73497329965393407729419051 110245994948090111594128577)
          ·
            refine ⟨82684496211067583695596433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110245994948090111594128577 82684496211067583695596433)
            ·
              refine ⟨62013372158300687771697325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82684496211067583695596433 62013372158300687771697325)
              ·
                refine ⟨23255014559362757914386497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62013372158300687771697325 23255014559362757914386497)
                ·
                  refine ⟨17441260919522068435789873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23255014559362757914386497 17441260919522068435789873)
                  ·
                    refine ⟨13080945689641551326842405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17441260919522068435789873 13080945689641551326842405)
                    ·
                      refine ⟨2452677316807790873782951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13080945689641551326842405 2452677316807790873782951)
                      ·
                        rfl

theorem cell23_4776572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_4776572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776572 prefixEnd_4776572 := by exact prefixLift 4776572
  have htrace : WordTrace (prefixWord ++ tailWord_4776572) baseStart_4776572 baseEnd_4776572 := by
    simpa [prefixWord, tailWord_4776572, baseEnd_4776572] using wordTrace_append hprefix tailTrace_4776572
  have hstable : (prefixWord ++ tailWord_4776572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776572).length < 2 ^ (prefixWord ++ tailWord_4776572).sum := by decide
  have hdescent : baseEnd_4776572 < baseStart_4776572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776592 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 3]
def baseStart_4776592 : Nat := 118140960795 + 4776592 * 2 ^ 59
def prefixEnd_4776592 : Nat := 4983230072969 + 3 ^ 40 * 4776592 * 2
def baseEnd_4776592 : Nat := 2452687586420880795532859

theorem tailTrace_4776592 : CollatzResearch.WordTrace tailWord_4776592 prefixEnd_4776592 2452687586420880795532859 := by
  unfold tailWord_4776592
  simp only [CollatzResearch.WordTrace]
  refine ⟨87108311355615217905694015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116144415140820290540925353 87108311355615217905694015)
  ·
    refine ⟨130662467033422826858541023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87108311355615217905694015 130662467033422826858541023)
    ·
      refine ⟨195993700550134240287811535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130662467033422826858541023 195993700550134240287811535)
      ·
        refine ⟨293990550825201360431717303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195993700550134240287811535 293990550825201360431717303)
        ·
          refine ⟨440985826237802040647575955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293990550825201360431717303 440985826237802040647575955)
          ·
            refine ⟨661478739356703060971363933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 440985826237802040647575955 661478739356703060971363933)
            ·
              refine ⟨248054527258763647864261475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 661478739356703060971363933 248054527258763647864261475)
              ·
                refine ⟨372081790888145471796392213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 248054527258763647864261475 372081790888145471796392213)
                ·
                  refine ⟨17441333947881818990455885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 372081790888145471796392213 17441333947881818990455885)
                  ·
                    refine ⟨6540500230455682121420957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17441333947881818990455885 6540500230455682121420957)
                    ·
                      refine ⟨2452687586420880795532859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6540500230455682121420957 2452687586420880795532859)
                      ·
                        rfl

theorem cell23_4776592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 3].length) (baseStart_4776592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776592 prefixEnd_4776592 := by exact prefixLift 4776592
  have htrace : WordTrace (prefixWord ++ tailWord_4776592) baseStart_4776592 baseEnd_4776592 := by
    simpa [prefixWord, tailWord_4776592, baseEnd_4776592] using wordTrace_append hprefix tailTrace_4776592
  have hstable : (prefixWord ++ tailWord_4776592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776592).length < 2 ^ (prefixWord ++ tailWord_4776592).sum := by decide
  have hdescent : baseEnd_4776592 < baseStart_4776592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776599 : List Nat := [1, 1, 3, 3, 2, 1, 2, 5, 5]
def baseStart_4776599 : Nat := 118140960795 + 4776599 * 2 ^ 59
def prefixEnd_4776599 : Nat := 4983230072969 + 3 ^ 40 * 4776599 * 2
def baseEnd_4776599 : Nat := 272521242309495807571703

theorem tailTrace_4776599 : CollatzResearch.WordTrace tailWord_4776599 prefixEnd_4776599 272521242309495807571703 := by
  unfold tailWord_4776599
  simp only [CollatzResearch.WordTrace]
  refine ⟨174216878022205076006892851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116144585348136717337928567 174216878022205076006892851)
  ·
    refine ⟨261325317033307614010339277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174216878022205076006892851 261325317033307614010339277)
    ·
      refine ⟨97996993887490355253877229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 261325317033307614010339277 97996993887490355253877229)
      ·
        refine ⟨36748872707808883220203961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97996993887490355253877229 36748872707808883220203961)
        ·
          refine ⟨27561654530856662415152971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36748872707808883220203961 27561654530856662415152971)
          ·
            refine ⟨41342481796284993622729457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27561654530856662415152971 41342481796284993622729457)
            ·
              refine ⟨31006861347213745217047093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41342481796284993622729457 31006861347213745217047093)
              ·
                refine ⟨2906893251301288614098165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31006861347213745217047093 2906893251301288614098165)
                ·
                  refine ⟨272521242309495807571703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2906893251301288614098165 272521242309495807571703)
                  ·
                    rfl

theorem cell23_4776599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 5, 5].length) (baseStart_4776599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776599 prefixEnd_4776599 := by exact prefixLift 4776599
  have htrace : WordTrace (prefixWord ++ tailWord_4776599) baseStart_4776599 baseEnd_4776599 := by
    simpa [prefixWord, tailWord_4776599, baseEnd_4776599] using wordTrace_append hprefix tailTrace_4776599
  have hstable : (prefixWord ++ tailWord_4776599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776599).length < 2 ^ (prefixWord ++ tailWord_4776599).sum := by decide
  have hdescent : baseEnd_4776599 < baseStart_4776599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776676 : List Nat := [2, 3, 1, 1, 1, 5, 2, 1, 3, 4]
def baseStart_4776676 : Nat := 118140960795 + 4776676 * 2 ^ 59
def prefixEnd_4776676 : Nat := 4983230072969 + 3 ^ 40 * 4776676 * 2
def baseEnd_4776676 : Nat := 817576906265286155627491

theorem tailTrace_4776676 : CollatzResearch.WordTrace tailWord_4776676 prefixEnd_4776676 817576906265286155627491 := by
  unfold tailWord_4776676
  simp only [CollatzResearch.WordTrace]
  refine ⟨87109843221463059078722941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116146457628617412104963921 87109843221463059078722941)
  ·
    refine ⟨32666191208048647154521103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87109843221463059078722941 32666191208048647154521103)
    ·
      refine ⟨48999286812072970731781655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32666191208048647154521103 48999286812072970731781655)
      ·
        refine ⟨73498930218109456097672483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48999286812072970731781655 73498930218109456097672483)
        ·
          refine ⟨110248395327164184146508725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73498930218109456097672483 110248395327164184146508725)
          ·
            refine ⟨10335787061921642263735193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 110248395327164184146508725 10335787061921642263735193)
            ·
              refine ⟨7751840296441231697801395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10335787061921642263735193 7751840296441231697801395)
              ·
                refine ⟨11627760444661847546702093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7751840296441231697801395 11627760444661847546702093)
                ·
                  refine ⟨4360410166748192830013285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11627760444661847546702093 4360410166748192830013285)
                  ·
                    refine ⟨817576906265286155627491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4360410166748192830013285 817576906265286155627491)
                    ·
                      rfl

theorem cell23_4776676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 3, 4].length) (baseStart_4776676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776676 prefixEnd_4776676 := by exact prefixLift 4776676
  have htrace : WordTrace (prefixWord ++ tailWord_4776676) baseStart_4776676 baseEnd_4776676 := by
    simpa [prefixWord, tailWord_4776676, baseEnd_4776676] using wordTrace_append hprefix tailTrace_4776676
  have hstable : (prefixWord ++ tailWord_4776676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776676).length < 2 ^ (prefixWord ++ tailWord_4776676).sum := by decide
  have hdescent : baseEnd_4776676 < baseStart_4776676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776719 : List Nat := [1, 1, 2, 1, 1, 1, 5, 5, 1, 5]
def baseStart_4776719 : Nat := 118140960795 + 4776719 * 2 ^ 59
def prefixEnd_4776719 : Nat := 4983230072969 + 3 ^ 40 * 4776719 * 2
def baseEnd_4776719 : Nat := 817584266154667266214925

theorem tailTrace_4776719 : CollatzResearch.WordTrace tailWord_4776719 prefixEnd_4776719 817584266154667266214925 := by
  unfold tailWord_4776719
  simp only [CollatzResearch.WordTrace]
  refine ⟨174221254781770336501261211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116147503187846891000840807 174221254781770336501261211)
  ·
    refine ⟨261331882172655504751891817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174221254781770336501261211 261331882172655504751891817)
    ·
      refine ⟨195998911629491628563918863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261331882172655504751891817 195998911629491628563918863)
      ·
        refine ⟨293998367444237442845878295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195998911629491628563918863 293998367444237442845878295)
        ·
          refine ⟨440997551166356164268817443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293998367444237442845878295 440997551166356164268817443)
          ·
            refine ⟨661496326749534246403226165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 440997551166356164268817443 661496326749534246403226165)
            ·
              refine ⟨62015280632768835600302453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 661496326749534246403226165 62015280632768835600302453)
              ·
                refine ⟨5813932559322078337528355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62015280632768835600302453 5813932559322078337528355)
                ·
                  refine ⟨8720898838983117506292533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5813932559322078337528355 8720898838983117506292533)
                  ·
                    refine ⟨817584266154667266214925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8720898838983117506292533 817584266154667266214925)
                    ·
                      rfl

theorem cell23_4776719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 5, 1, 5].length) (baseStart_4776719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776719 prefixEnd_4776719 := by exact prefixLift 4776719
  have htrace : WordTrace (prefixWord ++ tailWord_4776719) baseStart_4776719 baseEnd_4776719 := by
    simpa [prefixWord, tailWord_4776719, baseEnd_4776719] using wordTrace_append hprefix tailTrace_4776719
  have hstable : (prefixWord ++ tailWord_4776719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776719).length < 2 ^ (prefixWord ++ tailWord_4776719).sum := by decide
  have hdescent : baseEnd_4776719 < baseStart_4776719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776739 : List Nat := [1, 1, 1, 4, 2, 1, 1, 4, 3, 1, 4]
def baseStart_4776739 : Nat := 118140960795 + 4776739 * 2 ^ 59
def prefixEnd_4776739 : Nat := 4983230072969 + 3 ^ 40 * 4776739 * 2
def baseEnd_4776739 : Nat := 2452763068077091720394683

theorem tailTrace_4776739 : CollatzResearch.WordTrace tailWord_4776739 prefixEnd_4776739 2452763068077091720394683 := by
  unfold tailWord_4776739
  simp only [CollatzResearch.WordTrace]
  refine ⟨174221984241697879916989271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116147989494465253277992847 174221984241697879916989271)
  ·
    refine ⟨261332976362546819875483907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174221984241697879916989271 261332976362546819875483907)
    ·
      refine ⟨391999464543820229813225861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261332976362546819875483907 391999464543820229813225861)
      ·
        refine ⟨73499899601966293089979849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 391999464543820229813225861 73499899601966293089979849)
        ·
          refine ⟨55124924701474719817484887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73499899601966293089979849 55124924701474719817484887)
          ·
            refine ⟨82687387052212079726227331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55124924701474719817484887 82687387052212079726227331)
            ·
              refine ⟨124031080578318119589340997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82687387052212079726227331 124031080578318119589340997)
              ·
                refine ⟨23255827608434647423001437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 124031080578318119589340997 23255827608434647423001437)
                ·
                  refine ⟨8720935353162992783625539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23255827608434647423001437 8720935353162992783625539)
                  ·
                    refine ⟨13081403029744489175438309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8720935353162992783625539 13081403029744489175438309)
                    ·
                      refine ⟨2452763068077091720394683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13081403029744489175438309 2452763068077091720394683)
                      ·
                        rfl

theorem cell23_4776739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_4776739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776739 prefixEnd_4776739 := by exact prefixLift 4776739
  have htrace : WordTrace (prefixWord ++ tailWord_4776739) baseStart_4776739 baseEnd_4776739 := by
    simpa [prefixWord, tailWord_4776739, baseEnd_4776739] using wordTrace_append hprefix tailTrace_4776739
  have hstable : (prefixWord ++ tailWord_4776739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776739).length < 2 ^ (prefixWord ++ tailWord_4776739).sum := by decide
  have hdescent : baseEnd_4776739 < baseStart_4776739 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776740 : List Nat := [2, 3, 1, 3, 4, 1, 2, 1, 6]
def baseStart_4776740 : Nat := 118140960795 + 4776740 * 2 ^ 59
def prefixEnd_4776740 : Nat := 4983230072969 + 3 ^ 40 * 4776740 * 2
def baseEnd_4776740 : Nat := 272529286839749579609131

theorem tailTrace_4776740 : CollatzResearch.WordTrace tailWord_4776740 prefixEnd_4776740 272529286839749579609131 := by
  unfold tailWord_4776740
  simp only [CollatzResearch.WordTrace]
  refine ⟨87111010357347128543887837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116148013809796171391850449 87111010357347128543887837)
  ·
    refine ⟨32666628884005173203957939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87111010357347128543887837 32666628884005173203957939)
    ·
      refine ⟨48999943326007759805936909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32666628884005173203957939 48999943326007759805936909)
      ·
        refine ⟨18374978747252909927226341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48999943326007759805936909 18374978747252909927226341)
        ·
          refine ⟨3445308515109920611354939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18374978747252909927226341 3445308515109920611354939)
          ·
            refine ⟨5167962772664880917032409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3445308515109920611354939 5167962772664880917032409)
            ·
              refine ⟨3875972079498660687774307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5167962772664880917032409 3875972079498660687774307)
              ·
                refine ⟨5813958119247991031661461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3875972079498660687774307 5813958119247991031661461)
                ·
                  refine ⟨272529286839749579609131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5813958119247991031661461 272529286839749579609131)
                  ·
                    rfl

theorem cell23_4776740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 1, 6].length) (baseStart_4776740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776740 prefixEnd_4776740 := by exact prefixLift 4776740
  have htrace : WordTrace (prefixWord ++ tailWord_4776740) baseStart_4776740 baseEnd_4776740 := by
    simpa [prefixWord, tailWord_4776740, baseEnd_4776740] using wordTrace_append hprefix tailTrace_4776740
  have hstable : (prefixWord ++ tailWord_4776740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776740).length < 2 ^ (prefixWord ++ tailWord_4776740).sum := by decide
  have hdescent : baseEnd_4776740 < baseStart_4776740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776796 : List Nat := [2, 2, 4, 2, 1, 1, 3, 8]
def baseStart_4776796 : Nat := 118140960795 + 4776796 * 2 ^ 59
def prefixEnd_4776796 : Nat := 4983230072969 + 3 ^ 40 * 4776796 * 2
def baseEnd_4776796 : Nat := 90844160610162888791923

theorem tailTrace_4776796 : CollatzResearch.WordTrace tailWord_4776796 prefixEnd_4776796 90844160610162888791923 := by
  unfold tailWord_4776796
  simp only [CollatzResearch.WordTrace]
  refine ⟨87112031601245689325907121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116149375468327585767876161 87112031601245689325907121)
  ·
    refine ⟨65334023700934266994430341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87112031601245689325907121 65334023700934266994430341)
    ·
      refine ⟨12250129443925175061455689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65334023700934266994430341 12250129443925175061455689)
      ·
        refine ⟨9187597082943881296091767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12250129443925175061455689 9187597082943881296091767)
        ·
          refine ⟨13781395624415821944137651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9187597082943881296091767 13781395624415821944137651)
          ·
            refine ⟨20672093436623732916206477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13781395624415821944137651 20672093436623732916206477)
            ·
              refine ⟨7752035038733899843577429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20672093436623732916206477 7752035038733899843577429)
              ·
                refine ⟨90844160610162888791923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7752035038733899843577429 90844160610162888791923)
                ·
                  rfl

theorem cell23_4776796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 8].length) (baseStart_4776796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776796 prefixEnd_4776796 := by exact prefixLift 4776796
  have htrace : WordTrace (prefixWord ++ tailWord_4776796) baseStart_4776796 baseEnd_4776796 := by
    simpa [prefixWord, tailWord_4776796, baseEnd_4776796] using wordTrace_append hprefix tailTrace_4776796
  have hstable : (prefixWord ++ tailWord_4776796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776796).length < 2 ^ (prefixWord ++ tailWord_4776796).sum := by decide
  have hdescent : baseEnd_4776796 < baseStart_4776796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776834 : List Nat := [3, 4, 2, 2, 1, 2, 1, 2, 2, 4]
def baseStart_4776834 : Nat := 118140960795 + 4776834 * 2 ^ 59
def prefixEnd_4776834 : Nat := 4983230072969 + 3 ^ 40 * 4776834 * 2
def baseEnd_4776834 : Nat := 817603949579756282902249

theorem tailTrace_4776834 : CollatzResearch.WordTrace tailWord_4776834 prefixEnd_4776834 817603949579756282902249 := by
  unfold tailWord_4776834
  simp only [CollatzResearch.WordTrace]
  refine ⟨43556362294088427785424389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116150299450902474094465037 43556362294088427785424389)
  ·
    refine ⟨8166817930141580209767073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43556362294088427785424389 8166817930141580209767073)
    ·
      refine ⟨6125113447606185157325305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8166817930141580209767073 6125113447606185157325305)
      ·
        refine ⟨4593835085704638867993979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6125113447606185157325305 4593835085704638867993979)
        ·
          refine ⟨6890752628556958301990969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4593835085704638867993979 6890752628556958301990969)
          ·
            refine ⟨5168064471417718726493227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6890752628556958301990969 5168064471417718726493227)
            ·
              refine ⟨7752096707126578089739841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5168064471417718726493227 7752096707126578089739841)
              ·
                refine ⟨5814072530344933567304881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7752096707126578089739841 5814072530344933567304881)
                ·
                  refine ⟨4360554397758700175478661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5814072530344933567304881 4360554397758700175478661)
                  ·
                    refine ⟨817603949579756282902249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4360554397758700175478661 817603949579756282902249)
                    ·
                      rfl

theorem cell23_4776834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_4776834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776834 prefixEnd_4776834 := by exact prefixLift 4776834
  have htrace : WordTrace (prefixWord ++ tailWord_4776834) baseStart_4776834 baseEnd_4776834 := by
    simpa [prefixWord, tailWord_4776834, baseEnd_4776834] using wordTrace_append hprefix tailTrace_4776834
  have hstable : (prefixWord ++ tailWord_4776834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776834).length < 2 ^ (prefixWord ++ tailWord_4776834).sum := by decide
  have hdescent : baseEnd_4776834 < baseStart_4776834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776840 : List Nat := [2, 1, 3, 3, 2, 1, 3, 2, 2, 1, 3]
def baseStart_4776840 : Nat := 118140960795 + 4776840 * 2 ^ 59
def prefixEnd_4776840 : Nat := 4983230072969 + 3 ^ 40 * 4776840 * 2
def baseEnd_4776840 : Nat := 2452814929623195825231719

theorem tailTrace_4776840 : CollatzResearch.WordTrace tailWord_4776840 prefixEnd_4776840 2452814929623195825231719 := by
  unfold tailWord_4776840
  simp only [CollatzResearch.WordTrace]
  refine ⟨87112834007165987083207987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116150445342887982777610649 87112834007165987083207987)
  ·
    refine ⟨130669251010748980624811981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87112834007165987083207987 130669251010748980624811981)
    ·
      refine ⟨49000969129030867734304493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130669251010748980624811981 49000969129030867734304493)
      ·
        refine ⟨18375363423386575400364185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49000969129030867734304493 18375363423386575400364185)
        ·
          refine ⟨13781522567539931550273139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18375363423386575400364185 13781522567539931550273139)
          ·
            refine ⟨20672283851309897325409709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13781522567539931550273139 20672283851309897325409709)
            ·
              refine ⟨7752106444241211497028641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20672283851309897325409709 7752106444241211497028641)
              ·
                refine ⟨5814079833180908622771481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7752106444241211497028641 5814079833180908622771481)
                ·
                  refine ⟨4360559874885681467078611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5814079833180908622771481 4360559874885681467078611)
                  ·
                    refine ⟨6540839812328522200617917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4360559874885681467078611 6540839812328522200617917)
                    ·
                      refine ⟨2452814929623195825231719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6540839812328522200617917 2452814929623195825231719)
                      ·
                        rfl

theorem cell23_4776840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_4776840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776840 prefixEnd_4776840 := by exact prefixLift 4776840
  have htrace : WordTrace (prefixWord ++ tailWord_4776840) baseStart_4776840 baseEnd_4776840 := by
    simpa [prefixWord, tailWord_4776840, baseEnd_4776840] using wordTrace_append hprefix tailTrace_4776840
  have hstable : (prefixWord ++ tailWord_4776840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776840).length < 2 ^ (prefixWord ++ tailWord_4776840).sum := by decide
  have hdescent : baseEnd_4776840 < baseStart_4776840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776849 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 5]
def baseStart_4776849 : Nat := 118140960795 + 4776849 * 2 ^ 59
def prefixEnd_4776849 : Nat := 4983230072969 + 3 ^ 40 * 4776849 * 2
def baseEnd_4776849 : Nat := 2452819550949086290019177

theorem tailTrace_4776849 : CollatzResearch.WordTrace tailWord_4776849 prefixEnd_4776849 2452819550949086290019177 := by
  unfold tailWord_4776849
  simp only [CollatzResearch.WordTrace]
  refine ⟨174225996271299368703493601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116150664180866245802329067 174225996271299368703493601)
  ·
    refine ⟨130669497203474526527620201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174225996271299368703493601 130669497203474526527620201)
    ·
      refine ⟨98002122902605894895715151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130669497203474526527620201 98002122902605894895715151)
      ·
        refine ⟨147003184353908842343572727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98002122902605894895715151 147003184353908842343572727)
        ·
          refine ⟨220504776530863263515359091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147003184353908842343572727 220504776530863263515359091)
          ·
            refine ⟨330757164796294895273038637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220504776530863263515359091 330757164796294895273038637)
            ·
              refine ⟨124033936798610585727389489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 330757164796294895273038637 124033936798610585727389489)
              ·
                refine ⟨93025452598957939295542117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124033936798610585727389489 93025452598957939295542117)
                ·
                  refine ⟨17442272362304613617914147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93025452598957939295542117 17442272362304613617914147)
                  ·
                    refine ⟨26163408543456920426871221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17442272362304613617914147 26163408543456920426871221)
                    ·
                      refine ⟨2452819550949086290019177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26163408543456920426871221 2452819550949086290019177)
                      ·
                        rfl

theorem cell23_4776849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 5].length) (baseStart_4776849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776849 prefixEnd_4776849 := by exact prefixLift 4776849
  have htrace : WordTrace (prefixWord ++ tailWord_4776849) baseStart_4776849 baseEnd_4776849 := by
    simpa [prefixWord, tailWord_4776849, baseEnd_4776849] using wordTrace_append hprefix tailTrace_4776849
  have hstable : (prefixWord ++ tailWord_4776849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776849).length < 2 ^ (prefixWord ++ tailWord_4776849).sum := by decide
  have hdescent : baseEnd_4776849 < baseStart_4776849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776914 : List Nat := [3, 2, 2, 3, 1, 1, 4, 1, 2, 2, 2]
def baseStart_4776914 : Nat := 118140960795 + 4776914 * 2 ^ 59
def prefixEnd_4776914 : Nat := 4983230072969 + 3 ^ 40 * 4776914 * 2
def baseEnd_4776914 : Nat := 2452852927191628535706379

theorem tailTrace_4776914 : CollatzResearch.WordTrace tailWord_4776914 prefixEnd_4776914 2452852927191628535706379 := by
  unfold tailWord_4776914
  simp only [CollatzResearch.WordTrace]
  refine ⟨43557091754015971201152449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116152244677375923203073197 43557091754015971201152449)
  ·
    refine ⟨32667818815511978400864337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43557091754015971201152449 32667818815511978400864337)
    ·
      refine ⟨24500864111633983800648253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32667818815511978400864337 24500864111633983800648253)
      ·
        refine ⟨9187824041862743925243095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24500864111633983800648253 9187824041862743925243095)
        ·
          refine ⟨13781736062794115887864643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9187824041862743925243095 13781736062794115887864643)
          ·
            refine ⟨20672604094191173831796965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13781736062794115887864643 20672604094191173831796965)
            ·
              refine ⟨3876113267660845093461931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20672604094191173831796965 3876113267660845093461931)
              ·
                refine ⟨5814169901491267640192897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3876113267660845093461931 5814169901491267640192897)
                ·
                  refine ⟨4360627426118450730144673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5814169901491267640192897 4360627426118450730144673)
                  ·
                    refine ⟨3270470569588838047608505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4360627426118450730144673 3270470569588838047608505)
                    ·
                      refine ⟨2452852927191628535706379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3270470569588838047608505 2452852927191628535706379)
                      ·
                        rfl

theorem cell23_4776914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_4776914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776914 prefixEnd_4776914 := by exact prefixLift 4776914
  have htrace : WordTrace (prefixWord ++ tailWord_4776914) baseStart_4776914 baseEnd_4776914 := by
    simpa [prefixWord, tailWord_4776914, baseEnd_4776914] using wordTrace_append hprefix tailTrace_4776914
  have hstable : (prefixWord ++ tailWord_4776914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776914).length < 2 ^ (prefixWord ++ tailWord_4776914).sum := by decide
  have hdescent : baseEnd_4776914 < baseStart_4776914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776936 : List Nat := [2, 1, 4, 1, 1, 1, 2, 3, 1, 3, 4]
def baseStart_4776936 : Nat := 118140960795 + 4776936 * 2 ^ 59
def prefixEnd_4776936 : Nat := 4983230072969 + 3 ^ 40 * 4776936 * 2
def baseEnd_4776936 : Nat := 2452864223766027449631277

theorem tailTrace_4776936 : CollatzResearch.WordTrace tailWord_4776936 prefixEnd_4776936 2452864223766027449631277 := by
  unfold tailWord_4776936
  simp only [CollatzResearch.WordTrace]
  refine ⟨87114584710992091280955331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116152779614656121707940441 87114584710992091280955331)
  ·
    refine ⟨130671877066488136921432997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87114584710992091280955331 130671877066488136921432997)
    ·
      refine ⟨24500976949966525672768687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130671877066488136921432997 24500976949966525672768687)
      ·
        refine ⟨36751465424949788509153031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24500976949966525672768687 36751465424949788509153031)
        ·
          refine ⟨55127198137424682763729547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36751465424949788509153031 55127198137424682763729547)
          ·
            refine ⟨82690797206137024145594321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55127198137424682763729547 82690797206137024145594321)
            ·
              refine ⟨62018097904602768109195741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82690797206137024145594321 62018097904602768109195741)
              ·
                refine ⟨23256786714226038040948403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62018097904602768109195741 23256786714226038040948403)
                ·
                  refine ⟨34885180071339057061422605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23256786714226038040948403 34885180071339057061422605)
                  ·
                    refine ⟨13081942526752146398033477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34885180071339057061422605 13081942526752146398033477)
                    ·
                      refine ⟨2452864223766027449631277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13081942526752146398033477 2452864223766027449631277)
                      ·
                        rfl

theorem cell23_4776936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_4776936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776936 prefixEnd_4776936 := by exact prefixLift 4776936
  have htrace : WordTrace (prefixWord ++ tailWord_4776936) baseStart_4776936 baseEnd_4776936 := by
    simpa [prefixWord, tailWord_4776936, baseEnd_4776936] using wordTrace_append hprefix tailTrace_4776936
  have hstable : (prefixWord ++ tailWord_4776936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776936).length < 2 ^ (prefixWord ++ tailWord_4776936).sum := by decide
  have hdescent : baseEnd_4776936 < baseStart_4776936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776939 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 9]
def baseStart_4776939 : Nat := 118140960795 + 4776939 * 2 ^ 59
def prefixEnd_4776939 : Nat := 4983230072969 + 3 ^ 40 * 4776939 * 2
def baseEnd_4776939 : Nat := 2452865764207990937893763

theorem tailTrace_4776939 : CollatzResearch.WordTrace tailWord_4776939 prefixEnd_4776939 2452865764207990937893763 := by
  unfold tailWord_4776939
  simp only [CollatzResearch.WordTrace]
  refine ⟨174229278840973314074269871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116152852560648876049513247 174229278840973314074269871)
  ·
    refine ⟨261343918261459971111404807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174229278840973314074269871 261343918261459971111404807)
    ·
      refine ⟨392015877392189956667107211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261343918261459971111404807 392015877392189956667107211)
      ·
        refine ⟨588023816088284935000660817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 392015877392189956667107211 588023816088284935000660817)
        ·
          refine ⟨441017862066213701250495613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 588023816088284935000660817 441017862066213701250495613)
          ·
            refine ⟨165381698274830137968935855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 441017862066213701250495613 165381698274830137968935855)
            ·
              refine ⟨248072547412245206953403783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165381698274830137968935855 248072547412245206953403783)
              ·
                refine ⟨372108821118367810430105675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 248072547412245206953403783 372108821118367810430105675)
                ·
                  refine ⟨558163231677551715645158513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 372108821118367810430105675 558163231677551715645158513)
                  ·
                    refine ⟨418622423758163786733868885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 558163231677551715645158513 418622423758163786733868885)
                    ·
                      refine ⟨2452865764207990937893763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 418622423758163786733868885 2452865764207990937893763)
                      ·
                        rfl

theorem cell23_4776939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 9].length) (baseStart_4776939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776939 prefixEnd_4776939 := by exact prefixLift 4776939
  have htrace : WordTrace (prefixWord ++ tailWord_4776939) baseStart_4776939 baseEnd_4776939 := by
    simpa [prefixWord, tailWord_4776939, baseEnd_4776939] using wordTrace_append hprefix tailTrace_4776939
  have hstable : (prefixWord ++ tailWord_4776939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776939).length < 2 ^ (prefixWord ++ tailWord_4776939).sum := by decide
  have hdescent : baseEnd_4776939 < baseStart_4776939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776953 : List Nat := [1, 2, 1, 3, 1, 3, 2, 2, 2, 4, 2]
def baseStart_4776953 : Nat := 118140960795 + 4776953 * 2 ^ 59
def prefixEnd_4776953 : Nat := 4983230072969 + 3 ^ 40 * 4776953 * 2
def baseEnd_4776953 : Nat := 2452872952937153883118699

theorem tailTrace_4776953 : CollatzResearch.WordTrace tailWord_4776953 prefixEnd_4776953 2452872952937153883118699 := by
  unfold tailWord_4776953
  simp only [CollatzResearch.WordTrace]
  refine ⟨174229789462922594465279513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116153192975281729643519675 174229789462922594465279513)
  ·
    refine ⟨130672342097191945848959635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174229789462922594465279513 130672342097191945848959635)
    ·
      refine ⟨196008513145787918773439453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130672342097191945848959635 196008513145787918773439453)
      ·
        refine ⟨73503192429670469540039795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196008513145787918773439453 73503192429670469540039795)
        ·
          refine ⟨110254788644505704310059693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73503192429670469540039795 110254788644505704310059693)
          ·
            refine ⟨41345545741689639116272385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110254788644505704310059693 41345545741689639116272385)
            ·
              refine ⟨31009159306267229337204289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41345545741689639116272385 31009159306267229337204289)
              ·
                refine ⟨23256869479700422002903217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31009159306267229337204289 23256869479700422002903217)
                ·
                  refine ⟨17442652109775316502177413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23256869479700422002903217 17442652109775316502177413)
                  ·
                    refine ⟨3270497270582871844158265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17442652109775316502177413 3270497270582871844158265)
                    ·
                      refine ⟨2452872952937153883118699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3270497270582871844158265 2452872952937153883118699)
                      ·
                        rfl

theorem cell23_4776953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 4, 2].length) (baseStart_4776953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776953 prefixEnd_4776953 := by exact prefixLift 4776953
  have htrace : WordTrace (prefixWord ++ tailWord_4776953) baseStart_4776953 baseEnd_4776953 := by
    simpa [prefixWord, tailWord_4776953, baseEnd_4776953] using wordTrace_append hprefix tailTrace_4776953
  have hstable : (prefixWord ++ tailWord_4776953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776953).length < 2 ^ (prefixWord ++ tailWord_4776953).sum := by decide
  have hdescent : baseEnd_4776953 < baseStart_4776953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4776970 : List Nat := [3, 1, 2, 2, 3, 2, 1, 1, 2, 4, 2]
def baseStart_4776970 : Nat := 118140960795 + 4776970 * 2 ^ 59
def prefixEnd_4776970 : Nat := 4983230072969 + 3 ^ 40 * 4776970 * 2
def baseEnd_4776970 : Nat := 2452881682108280316606121

theorem tailTrace_4776970 : CollatzResearch.WordTrace tailWord_4776970 prefixEnd_4776970 2452881682108280316606121 := by
  unfold tailWord_4776970
  simp only [CollatzResearch.WordTrace]
  refine ⟨43557602375965251592162091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116153606335907337579098909 43557602375965251592162091)
  ·
    refine ⟨65336403563947877388243137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43557602375965251592162091 65336403563947877388243137)
    ·
      refine ⟨49002302672960908041182353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65336403563947877388243137 49002302672960908041182353)
      ·
        refine ⟨36751727004720681030886765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49002302672960908041182353 36751727004720681030886765)
        ·
          refine ⟨13781897626770255386582537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36751727004720681030886765 13781897626770255386582537)
          ·
            refine ⟨10336423220077691539936903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13781897626770255386582537 10336423220077691539936903)
            ·
              refine ⟨15504634830116537309905355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10336423220077691539936903 15504634830116537309905355)
              ·
                refine ⟨23256952245174805964858033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15504634830116537309905355 23256952245174805964858033)
                ·
                  refine ⟨17442714183881104473643525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23256952245174805964858033 17442714183881104473643525)
                  ·
                    refine ⟨3270508909477707088808161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17442714183881104473643525 3270508909477707088808161)
                    ·
                      refine ⟨2452881682108280316606121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3270508909477707088808161 2452881682108280316606121)
                      ·
                        rfl

theorem cell23_4776970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 2, 4, 2].length) (baseStart_4776970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4776970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4776970 prefixEnd_4776970 := by exact prefixLift 4776970
  have htrace : WordTrace (prefixWord ++ tailWord_4776970) baseStart_4776970 baseEnd_4776970 := by
    simpa [prefixWord, tailWord_4776970, baseEnd_4776970] using wordTrace_append hprefix tailTrace_4776970
  have hstable : (prefixWord ++ tailWord_4776970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4776970).length < 2 ^ (prefixWord ++ tailWord_4776970).sum := by decide
  have hdescent : baseEnd_4776970 < baseStart_4776970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4776970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777003 : List Nat := [1, 1, 1, 1, 2, 1, 5, 2, 5, 1, 3]
def baseStart_4777003 : Nat := 118140960795 + 4777003 * 2 ^ 59
def prefixEnd_4777003 : Nat := 4983230072969 + 3 ^ 40 * 4777003 * 2
def baseEnd_4777003 : Nat := 2452898626969878687493469

theorem tailTrace_4777003 : CollatzResearch.WordTrace tailWord_4777003 prefixEnd_4777003 2452898626969878687493469 := by
  unfold tailWord_4777003
  simp only [CollatzResearch.WordTrace]
  refine ⟨174231613112741453004599663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116154408741827635336399775 174231613112741453004599663)
  ·
    refine ⟨261347419669112179506899495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174231613112741453004599663 261347419669112179506899495)
    ·
      refine ⟨392021129503668269260349243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261347419669112179506899495 392021129503668269260349243)
      ·
        refine ⟨588031694255502403890523865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 392021129503668269260349243 588031694255502403890523865)
        ·
          refine ⟨441023770691626802917892899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 588031694255502403890523865 441023770691626802917892899)
          ·
            refine ⟨661535656037440204376839349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 441023770691626802917892899 661535656037440204376839349)
            ·
              refine ⟨62018967753510019160328689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 661535656037440204376839349 62018967753510019160328689)
              ·
                refine ⟨46514225815132514370246517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62018967753510019160328689 46514225815132514370246517)
                ·
                  refine ⟨4360708670168673222210611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46514225815132514370246517 4360708670168673222210611)
                  ·
                    refine ⟨6541063005253009833315917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4360708670168673222210611 6541063005253009833315917)
                    ·
                      refine ⟨2452898626969878687493469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6541063005253009833315917 2452898626969878687493469)
                      ·
                        rfl

theorem cell23_4777003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 5, 1, 3].length) (baseStart_4777003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777003 prefixEnd_4777003 := by exact prefixLift 4777003
  have htrace : WordTrace (prefixWord ++ tailWord_4777003) baseStart_4777003 baseEnd_4777003 := by
    simpa [prefixWord, tailWord_4777003, baseEnd_4777003] using wordTrace_append hprefix tailTrace_4777003
  have hstable : (prefixWord ++ tailWord_4777003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777003).length < 2 ^ (prefixWord ++ tailWord_4777003).sum := by decide
  have hdescent : baseEnd_4777003 < baseStart_4777003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777020 : List Nat := [2, 2, 2, 2, 2, 2, 1, 3, 3, 1, 3]
def baseStart_4777020 : Nat := 118140960795 + 4777020 * 2 ^ 59
def prefixEnd_4777020 : Nat := 4983230072969 + 3 ^ 40 * 4777020 * 2
def baseEnd_4777020 : Nat := 2452907356141005120980891

theorem tailTrace_4777020 : CollatzResearch.WordTrace tailWord_4777020 prefixEnd_4777020 2452907356141005120980891 := by
  unfold tailWord_4777020
  simp only [CollatzResearch.WordTrace]
  refine ⟨87116116576839932453984257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116154822102453243271979009 87116116576839932453984257)
  ·
    refine ⟨65337087432629949340488193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87116116576839932453984257 65337087432629949340488193)
    ·
      refine ⟨49002815574472462005366145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65337087432629949340488193 49002815574472462005366145)
      ·
        refine ⟨36752111680854346504024609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49002815574472462005366145 36752111680854346504024609)
        ·
          refine ⟨27564083760640759878018457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36752111680854346504024609 27564083760640759878018457)
          ·
            refine ⟨20673062820480569908513843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27564083760640759878018457 20673062820480569908513843)
            ·
              refine ⟨31009594230720854862770765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20673062820480569908513843 31009594230720854862770765)
              ·
                refine ⟨11628597836520320573539037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31009594230720854862770765 11628597836520320573539037)
                ·
                  refine ⟨4360724188695120215077139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11628597836520320573539037 4360724188695120215077139)
                  ·
                    refine ⟨6541086283042680322615709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4360724188695120215077139 6541086283042680322615709)
                    ·
                      refine ⟨2452907356141005120980891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6541086283042680322615709 2452907356141005120980891)
                      ·
                        rfl

theorem cell23_4777020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_4777020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777020 prefixEnd_4777020 := by exact prefixLift 4777020
  have htrace : WordTrace (prefixWord ++ tailWord_4777020) baseStart_4777020 baseEnd_4777020 := by
    simpa [prefixWord, tailWord_4777020, baseEnd_4777020] using wordTrace_append hprefix tailTrace_4777020
  have hstable : (prefixWord ++ tailWord_4777020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777020).length < 2 ^ (prefixWord ++ tailWord_4777020).sum := by decide
  have hdescent : baseEnd_4777020 < baseStart_4777020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777037 : List Nat := [1, 6, 1, 1, 1, 2, 2, 2, 3, 1, 3]
def baseStart_4777037 : Nat := 118140960795 + 4777037 * 2 ^ 59
def prefixEnd_4777037 : Nat := 4983230072969 + 3 ^ 40 * 4777037 * 2
def baseEnd_4777037 : Nat := 2452916085312131554468313

theorem tailTrace_4777037 : CollatzResearch.WordTrace tailWord_4777037 prefixEnd_4777037 2452916085312131554468313 := by
  unfold tailWord_4777037
  simp only [CollatzResearch.WordTrace]
  refine ⟨174232853194618276811337365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116155235463078851207558243 174232853194618276811337365)
  ·
    refine ⟨8167164993497731725531439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 174232853194618276811337365 8167164993497731725531439)
    ·
      refine ⟨12250747490246597588297159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8167164993497731725531439 12250747490246597588297159)
      ·
        refine ⟨18376121235369896382445739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12250747490246597588297159 18376121235369896382445739)
        ·
          refine ⟨27564181853054844573668609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18376121235369896382445739 27564181853054844573668609)
          ·
            refine ⟨20673136389791133430251457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27564181853054844573668609 20673136389791133430251457)
            ·
              refine ⟨15504852292343350072688593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20673136389791133430251457 15504852292343350072688593)
              ·
                refine ⟨11628639219257512554516445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15504852292343350072688593 11628639219257512554516445)
                ·
                  refine ⟨4360739707221567207943667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11628639219257512554516445 4360739707221567207943667)
                  ·
                    refine ⟨6541109560832350811915501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4360739707221567207943667 6541109560832350811915501)
                    ·
                      refine ⟨2452916085312131554468313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6541109560832350811915501 2452916085312131554468313)
                      ·
                        rfl

theorem cell23_4777037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_4777037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777037 prefixEnd_4777037 := by exact prefixLift 4777037
  have htrace : WordTrace (prefixWord ++ tailWord_4777037) baseStart_4777037 baseEnd_4777037 := by
    simpa [prefixWord, tailWord_4777037, baseEnd_4777037] using wordTrace_append hprefix tailTrace_4777037
  have hstable : (prefixWord ++ tailWord_4777037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777037).length < 2 ^ (prefixWord ++ tailWord_4777037).sum := by decide
  have hdescent : baseEnd_4777037 < baseStart_4777037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777043 : List Nat := [1, 1, 1, 2, 1, 1, 2, 8, 1, 1, 4]
def baseStart_4777043 : Nat := 118140960795 + 4777043 * 2 ^ 59
def prefixEnd_4777043 : Nat := 4983230072969 + 3 ^ 40 * 4777043 * 2
def baseEnd_4777043 : Nat := 2452919166196058530993285

theorem tailTrace_4777043 : CollatzResearch.WordTrace tailWord_4777043 prefixEnd_4777043 2452919166196058530993285 := by
  unfold tailWord_4777043
  simp only [CollatzResearch.WordTrace]
  refine ⟨174233072032596539836055783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116155381355064359890703855 174233072032596539836055783)
  ·
    refine ⟨261349608048894809754083675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174233072032596539836055783 261349608048894809754083675)
    ·
      refine ⟨392024412073342214631125513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261349608048894809754083675 392024412073342214631125513)
      ·
        refine ⟨294018309055006660973344135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 392024412073342214631125513 294018309055006660973344135)
        ·
          refine ⟨441027463582509991460016203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294018309055006660973344135 441027463582509991460016203)
          ·
            refine ⟨661541195373764987190024305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 441027463582509991460016203 661541195373764987190024305)
            ·
              refine ⟨496155896530323740392518229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 661541195373764987190024305 496155896530323740392518229)
              ·
                refine ⟨5814326912464731332724823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 496155896530323740392518229 5814326912464731332724823)
                ·
                  refine ⟨8721490368697096999087235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5814326912464731332724823 8721490368697096999087235)
                  ·
                    refine ⟨13082235553045645498630853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8721490368697096999087235 13082235553045645498630853)
                    ·
                      refine ⟨2452919166196058530993285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13082235553045645498630853 2452919166196058530993285)
                      ·
                        rfl

theorem cell23_4777043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 8, 1, 1, 4].length) (baseStart_4777043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777043 prefixEnd_4777043 := by exact prefixLift 4777043
  have htrace : WordTrace (prefixWord ++ tailWord_4777043) baseStart_4777043 baseEnd_4777043 := by
    simpa [prefixWord, tailWord_4777043, baseEnd_4777043] using wordTrace_append hprefix tailTrace_4777043
  have hstable : (prefixWord ++ tailWord_4777043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777043).length < 2 ^ (prefixWord ++ tailWord_4777043).sum := by decide
  have hdescent : baseEnd_4777043 < baseStart_4777043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777063 : List Nat := [1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 5]
def baseStart_4777063 : Nat := 118140960795 + 4777063 * 2 ^ 59
def prefixEnd_4777063 : Nat := 4983230072969 + 3 ^ 40 * 4777063 * 2
def baseEnd_4777063 : Nat := 2452929435809148452743193

theorem tailTrace_4777063 : CollatzResearch.WordTrace tailWord_4777063 prefixEnd_4777063 2452929435809148452743193 := by
  unfold tailWord_4777063
  simp only [CollatzResearch.WordTrace]
  refine ⟨174233801492524083251783843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116155867661682722167855895 174233801492524083251783843)
  ·
    refine ⟨261350702238786124877675765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174233801492524083251783843 261350702238786124877675765)
    ·
      refine ⟨24501628334886199207282103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 261350702238786124877675765 24501628334886199207282103)
      ·
        refine ⟨36752442502329298810923155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24501628334886199207282103 36752442502329298810923155)
        ·
          refine ⟨55128663753493948216384733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36752442502329298810923155 55128663753493948216384733)
          ·
            refine ⟨20673248907560230581144275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55128663753493948216384733 20673248907560230581144275)
            ·
              refine ⟨31009873361340345871716413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20673248907560230581144275 31009873361340345871716413)
              ·
                refine ⟨11628702510502629701893655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31009873361340345871716413 11628702510502629701893655)
                ·
                  refine ⟨17443053765753944552840483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11628702510502629701893655 17443053765753944552840483)
                  ·
                    refine ⟨26164580648630916829260725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17443053765753944552840483 26164580648630916829260725)
                    ·
                      refine ⟨2452929435809148452743193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26164580648630916829260725 2452929435809148452743193)
                      ·
                        rfl

theorem cell23_4777063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_4777063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777063 prefixEnd_4777063 := by exact prefixLift 4777063
  have htrace : WordTrace (prefixWord ++ tailWord_4777063) baseStart_4777063 baseEnd_4777063 := by
    simpa [prefixWord, tailWord_4777063, baseEnd_4777063] using wordTrace_append hprefix tailTrace_4777063
  have hstable : (prefixWord ++ tailWord_4777063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777063).length < 2 ^ (prefixWord ++ tailWord_4777063).sum := by decide
  have hdescent : baseEnd_4777063 < baseStart_4777063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777064 : List Nat := [2, 1, 4, 4, 1, 1, 1, 2, 2, 3, 2]
def baseStart_4777064 : Nat := 118140960795 + 4777064 * 2 ^ 59
def prefixEnd_4777064 : Nat := 4983230072969 + 3 ^ 40 * 4777064 * 2
def baseEnd_4777064 : Nat := 2452929949289802948830689

theorem tailTrace_4777064 : CollatzResearch.WordTrace tailWord_4777064 prefixEnd_4777064 2452929949289802948830689 := by
  unfold tailWord_4777064
  simp only [CollatzResearch.WordTrace]
  refine ⟨87116918982760230211285123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116155891977013640281713497 87116918982760230211285123)
  ·
    refine ⟨130675378474140345316927685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87116918982760230211285123 130675378474140345316927685)
    ·
      refine ⟨24501633463901314746923941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130675378474140345316927685 24501633463901314746923941)
      ·
        refine ⟨4594056274481496515048239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24501633463901314746923941 4594056274481496515048239)
        ·
          refine ⟨6891084411722244772572359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4594056274481496515048239 6891084411722244772572359)
          ·
            refine ⟨10336626617583367158858539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6891084411722244772572359 10336626617583367158858539)
            ·
              refine ⟨15504939926375050738287809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10336626617583367158858539 15504939926375050738287809)
              ·
                refine ⟨11628704944781288053715857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15504939926375050738287809 11628704944781288053715857)
                ·
                  refine ⟨8721528708585966040286893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11628704944781288053715857 8721528708585966040286893)
                  ·
                    refine ⟨3270573265719737265107585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8721528708585966040286893 3270573265719737265107585)
                    ·
                      refine ⟨2452929949289802948830689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3270573265719737265107585 2452929949289802948830689)
                      ·
                        rfl

theorem cell23_4777064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_4777064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777064 prefixEnd_4777064 := by exact prefixLift 4777064
  have htrace : WordTrace (prefixWord ++ tailWord_4777064) baseStart_4777064 baseEnd_4777064 := by
    simpa [prefixWord, tailWord_4777064, baseEnd_4777064] using wordTrace_append hprefix tailTrace_4777064
  have hstable : (prefixWord ++ tailWord_4777064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777064).length < 2 ^ (prefixWord ++ tailWord_4777064).sum := by decide
  have hdescent : baseEnd_4777064 < baseStart_4777064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777070 : List Nat := [4, 1, 2, 2, 1, 2, 2, 1, 4, 4]
def baseStart_4777070 : Nat := 118140960795 + 4777070 * 2 ^ 59
def prefixEnd_4777070 : Nat := 4983230072969 + 3 ^ 40 * 4777070 * 2
def baseEnd_4777070 : Nat := 817644343391243308451887

theorem tailTrace_4777070 : CollatzResearch.WordTrace tailWord_4777070 prefixEnd_4777070 817644343391243308451887 := by
  unfold tailWord_4777070
  simp only [CollatzResearch.WordTrace]
  refine ⟨21779257100437340430911083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116156037868999148964859109 21779257100437340430911083)
  ·
    refine ⟨32668885650656010646366625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21779257100437340430911083 32668885650656010646366625)
    ·
      refine ⟨24501664237992007984774969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32668885650656010646366625 24501664237992007984774969)
      ·
        refine ⟨18376248178494005988581227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24501664237992007984774969 18376248178494005988581227)
        ·
          refine ⟨27564372267741008982871841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18376248178494005988581227 27564372267741008982871841)
          ·
            refine ⟨20673279200805756737153881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27564372267741008982871841 20673279200805756737153881)
            ·
              refine ⟨15504959400604317552865411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20673279200805756737153881 15504959400604317552865411)
              ·
                refine ⟨23257439100906476329298117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15504959400604317552865411 23257439100906476329298117)
                ·
                  refine ⟨4360769831419964311743397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23257439100906476329298117 4360769831419964311743397)
                  ·
                    refine ⟨817644343391243308451887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4360769831419964311743397 817644343391243308451887)
                    ·
                      rfl

theorem cell23_4777070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_4777070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777070 prefixEnd_4777070 := by exact prefixLift 4777070
  have htrace : WordTrace (prefixWord ++ tailWord_4777070) baseStart_4777070 baseEnd_4777070 := by
    simpa [prefixWord, tailWord_4777070, baseEnd_4777070] using wordTrace_append hprefix tailTrace_4777070
  have hstable : (prefixWord ++ tailWord_4777070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777070).length < 2 ^ (prefixWord ++ tailWord_4777070).sum := by decide
  have hdescent : baseEnd_4777070 < baseStart_4777070 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777097 : List Nat := [1, 2, 1, 1, 4, 5, 1, 2, 1, 2, 3]
def baseStart_4777097 : Nat := 118140960795 + 4777097 * 2 ^ 59
def prefixEnd_4777097 : Nat := 4983230072969 + 3 ^ 40 * 4777097 * 2
def baseEnd_4777097 : Nat := 2452946894151401319718037

theorem tailTrace_4777097 : CollatzResearch.WordTrace tailWord_4777097 prefixEnd_4777097 2452946894151401319718037 := by
  unfold tailWord_4777097
  simp only [CollatzResearch.WordTrace]
  refine ⟨174235041574400907058521545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116156694382933938039014363 174235041574400907058521545)
  ·
    refine ⟨130676281180800680293891159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174235041574400907058521545 130676281180800680293891159)
    ·
      refine ⟨196014421771201020440836739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130676281180800680293891159 196014421771201020440836739)
      ·
        refine ⟨294021632656801530661255109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196014421771201020440836739 294021632656801530661255109)
        ·
          refine ⟨55129056123150286998985333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 294021632656801530661255109 55129056123150286998985333)
          ·
            refine ⟨5168349011545339406154875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55129056123150286998985333 5168349011545339406154875)
            ·
              refine ⟨7752523517318009109232313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5168349011545339406154875 7752523517318009109232313)
              ·
                refine ⟨5814392637988506831924235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7752523517318009109232313 5814392637988506831924235)
                ·
                  refine ⟨8721588956982760247886353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5814392637988506831924235 8721588956982760247886353)
                  ·
                    refine ⟨6541191717737070185914765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8721588956982760247886353 6541191717737070185914765)
                    ·
                      refine ⟨2452946894151401319718037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6541191717737070185914765 2452946894151401319718037)
                      ·
                        rfl

theorem cell23_4777097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 2, 1, 2, 3].length) (baseStart_4777097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777097 prefixEnd_4777097 := by exact prefixLift 4777097
  have htrace : WordTrace (prefixWord ++ tailWord_4777097) baseStart_4777097 baseEnd_4777097 := by
    simpa [prefixWord, tailWord_4777097, baseEnd_4777097] using wordTrace_append hprefix tailTrace_4777097
  have hstable : (prefixWord ++ tailWord_4777097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777097).length < 2 ^ (prefixWord ++ tailWord_4777097).sum := by decide
  have hdescent : baseEnd_4777097 < baseStart_4777097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777114 : List Nat := [3, 1, 1, 5, 1, 2, 3, 1, 1, 2, 3]
def baseStart_4777114 : Nat := 118140960795 + 4777114 * 2 ^ 59
def prefixEnd_4777114 : Nat := 4983230072969 + 3 ^ 40 * 4777114 * 2
def baseEnd_4777114 : Nat := 2452955623322527753205459

theorem tailTrace_4777114 : CollatzResearch.WordTrace tailWord_4777114 prefixEnd_4777114 2452955623322527753205459 := by
  unfold tailWord_4777114
  simp only [CollatzResearch.WordTrace]
  refine ⟨43558915403834829740472599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116157107743559545974593597 43558915403834829740472599)
  ·
    refine ⟨65338373105752244610708899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43558915403834829740472599 65338373105752244610708899)
    ·
      refine ⟨98007559658628366916063349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65338373105752244610708899 98007559658628366916063349)
      ·
        refine ⟨9188208717996409398380939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 98007559658628366916063349 9188208717996409398380939)
        ·
          refine ⟨13782313076994614097571409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9188208717996409398380939 13782313076994614097571409)
          ·
            refine ⟨10336734807745960573178557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13782313076994614097571409 10336734807745960573178557)
            ·
              refine ⟨3876275552904735214941959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10336734807745960573178557 3876275552904735214941959)
              ·
                refine ⟨5814413329357102822412939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3876275552904735214941959 5814413329357102822412939)
                ·
                  refine ⟨8721619994035654233619409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5814413329357102822412939 8721619994035654233619409)
                  ·
                    refine ⟨6541214995526740675214557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8721619994035654233619409 6541214995526740675214557)
                    ·
                      refine ⟨2452955623322527753205459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6541214995526740675214557 2452955623322527753205459)
                      ·
                        rfl

theorem cell23_4777114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_4777114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777114 prefixEnd_4777114 := by exact prefixLift 4777114
  have htrace : WordTrace (prefixWord ++ tailWord_4777114) baseStart_4777114 baseEnd_4777114 := by
    simpa [prefixWord, tailWord_4777114, baseEnd_4777114] using wordTrace_append hprefix tailTrace_4777114
  have hstable : (prefixWord ++ tailWord_4777114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777114).length < 2 ^ (prefixWord ++ tailWord_4777114).sum := by decide
  have hdescent : baseEnd_4777114 < baseStart_4777114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777130 : List Nat := [3, 1, 5, 1, 1, 1, 1, 1, 2, 7]
def baseStart_4777130 : Nat := 118140960795 + 4777130 * 2 ^ 59
def prefixEnd_4777130 : Nat := 4983230072969 + 3 ^ 40 * 4777130 * 2
def baseEnd_4777130 : Nat := 817654613004333230201795

theorem tailTrace_4777130 : CollatzResearch.WordTrace tailWord_4777130 prefixEnd_4777130 817654613004333230201795 := by
  unfold tailWord_4777130
  simp only [CollatzResearch.WordTrace]
  refine ⟨43559061295820338423618211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116157496788854235796315229 43559061295820338423618211)
  ·
    refine ⟨65338591943730507635427317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43559061295820338423618211 65338591943730507635427317)
    ·
      refine ⟨6125492994724735090821311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65338591943730507635427317 6125492994724735090821311)
      ·
        refine ⟨9188239492087102636231967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6125492994724735090821311 9188239492087102636231967)
        ·
          refine ⟨13782359238130653954347951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9188239492087102636231967 13782359238130653954347951)
          ·
            refine ⟨20673538857195980931521927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13782359238130653954347951 20673538857195980931521927)
            ·
              refine ⟨31010308285793971397282891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20673538857195980931521927 31010308285793971397282891)
              ·
                refine ⟨46515462428690957095924337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31010308285793971397282891 46515462428690957095924337)
                ·
                  refine ⟨34886596821518217821943253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46515462428690957095924337 34886596821518217821943253)
                  ·
                    refine ⟨817654613004333230201795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34886596821518217821943253 817654613004333230201795)
                    ·
                      rfl

theorem cell23_4777130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_4777130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777130 prefixEnd_4777130 := by exact prefixLift 4777130
  have htrace : WordTrace (prefixWord ++ tailWord_4777130) baseStart_4777130 baseEnd_4777130 := by
    simpa [prefixWord, tailWord_4777130, baseEnd_4777130] using wordTrace_append hprefix tailTrace_4777130
  have hstable : (prefixWord ++ tailWord_4777130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777130).length < 2 ^ (prefixWord ++ tailWord_4777130).sum := by decide
  have hdescent : baseEnd_4777130 < baseStart_4777130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777137 : List Nat := [1, 2, 2, 5, 1, 1, 1, 2, 3, 3, 2]
def baseStart_4777137 : Nat := 118140960795 + 4777137 * 2 ^ 59
def prefixEnd_4777137 : Nat := 4983230072969 + 3 ^ 40 * 4777137 * 2
def baseEnd_4777137 : Nat := 2452967433377581163217853

theorem tailTrace_4777137 : CollatzResearch.WordTrace tailWord_4777137 prefixEnd_4777137 2452967433377581163217853 := by
  unfold tailWord_4777137
  simp only [CollatzResearch.WordTrace]
  refine ⟨174236500494255993889977665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116157666996170662593318443 174236500494255993889977665)
  ·
    refine ⟨130677375370691995417483249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174236500494255993889977665 130677375370691995417483249)
    ·
      refine ⟨98008031528018996563112437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130677375370691995417483249 98008031528018996563112437)
      ·
        refine ⟨9188252955751780927791791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 98008031528018996563112437 9188252955751780927791791)
        ·
          refine ⟨13782379433627671391687687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9188252955751780927791791 13782379433627671391687687)
          ·
            refine ⟨20673569150441507087531531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13782379433627671391687687 20673569150441507087531531)
            ·
              refine ⟨31010353725662260631297297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20673569150441507087531531 31010353725662260631297297)
              ·
                refine ⟨23257765294246695473472973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31010353725662260631297297 23257765294246695473472973)
                ·
                  refine ⟨8721661985342510802552365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23257765294246695473472973 8721661985342510802552365)
                  ·
                    refine ⟨3270623244503441550957137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8721661985342510802552365 3270623244503441550957137)
                    ·
                      refine ⟨2452967433377581163217853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3270623244503441550957137 2452967433377581163217853)
                      ·
                        rfl

theorem cell23_4777137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_4777137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777137 prefixEnd_4777137 := by exact prefixLift 4777137
  have htrace : WordTrace (prefixWord ++ tailWord_4777137) baseStart_4777137 baseEnd_4777137 := by
    simpa [prefixWord, tailWord_4777137, baseEnd_4777137] using wordTrace_append hprefix tailTrace_4777137
  have hstable : (prefixWord ++ tailWord_4777137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777137).length < 2 ^ (prefixWord ++ tailWord_4777137).sum := by decide
  have hdescent : baseEnd_4777137 < baseStart_4777137 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777143 : List Nat := [1, 1, 3, 1, 4, 1, 3, 1, 2, 6]
def baseStart_4777143 : Nat := 118140960795 + 4777143 * 2 ^ 59
def prefixEnd_4777143 : Nat := 4983230072969 + 3 ^ 40 * 4777143 * 2
def baseEnd_4777143 : Nat := 817656838087169379914275

theorem tailTrace_4777143 : CollatzResearch.WordTrace tailWord_4777143 prefixEnd_4777143 817656838087169379914275 := by
  unfold tailWord_4777143
  simp only [CollatzResearch.WordTrace]
  refine ⟨174236719332234256914696083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116157812888156171276464055 174236719332234256914696083)
  ·
    refine ⟨261355078998351385372044125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174236719332234256914696083 261355078998351385372044125)
    ·
      refine ⟨98008154624381769514516547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 261355078998351385372044125 98008154624381769514516547)
      ·
        refine ⟨147012231936572654271774821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98008154624381769514516547 147012231936572654271774821)
        ·
          refine ⟨27564793488107372675957779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 147012231936572654271774821 27564793488107372675957779)
          ·
            refine ⟨41347190232161059013936669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27564793488107372675957779 41347190232161059013936669)
            ·
              refine ⟨15505196337060397130226251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41347190232161059013936669 15505196337060397130226251)
              ·
                refine ⟨23257794505590595695339377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15505196337060397130226251 23257794505590595695339377)
                ·
                  refine ⟨17443345879192946771504533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23257794505590595695339377 17443345879192946771504533)
                  ·
                    refine ⟨817656838087169379914275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17443345879192946771504533 817656838087169379914275)
                    ·
                      rfl

theorem cell23_4777143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 6].length) (baseStart_4777143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777143 prefixEnd_4777143 := by exact prefixLift 4777143
  have htrace : WordTrace (prefixWord ++ tailWord_4777143) baseStart_4777143 baseEnd_4777143 := by
    simpa [prefixWord, tailWord_4777143, baseEnd_4777143] using wordTrace_append hprefix tailTrace_4777143
  have hstable : (prefixWord ++ tailWord_4777143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777143).length < 2 ^ (prefixWord ++ tailWord_4777143).sum := by decide
  have hdescent : baseEnd_4777143 < baseStart_4777143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777165 : List Nat := [1, 6, 2, 2, 2, 1, 2, 1, 1, 2, 3]
def baseStart_4777165 : Nat := 118140960795 + 4777165 * 2 ^ 59
def prefixEnd_4777165 : Nat := 4983230072969 + 3 ^ 40 * 4777165 * 2
def baseEnd_4777165 : Nat := 2452981810835907053667725

theorem tailTrace_4777165 : CollatzResearch.WordTrace tailWord_4777165 prefixEnd_4777165 2452981810835907053667725 := by
  unfold tailWord_4777165
  simp only [CollatzResearch.WordTrace]
  refine ⟨174237521738154554671996949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116158347825436369781331299 174237521738154554671996949)
  ·
    refine ⟨8167383831475994750249857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 174237521738154554671996949 8167383831475994750249857)
    ·
      refine ⟨6125537873606996062687393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8167383831475994750249857 6125537873606996062687393)
      ·
        refine ⟨4594153405205247047015545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6125537873606996062687393 4594153405205247047015545)
        ·
          refine ⟨3445615053903935285261659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4594153405205247047015545 3445615053903935285261659)
          ·
            refine ⟨5168422580855902927892489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3445615053903935285261659 5168422580855902927892489)
            ·
              refine ⟨3876316935641927195919367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5168422580855902927892489 3876316935641927195919367)
              ·
                refine ⟨5814475403462890793879051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3876316935641927195919367 5814475403462890793879051)
                ·
                  refine ⟨8721713105194336190818577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5814475403462890793879051 8721713105194336190818577)
                  ·
                    refine ⟨6541284828895752143113933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8721713105194336190818577 6541284828895752143113933)
                    ·
                      refine ⟨2452981810835907053667725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6541284828895752143113933 2452981810835907053667725)
                      ·
                        rfl

theorem cell23_4777165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_4777165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777165 prefixEnd_4777165 := by exact prefixLift 4777165
  have htrace : WordTrace (prefixWord ++ tailWord_4777165) baseStart_4777165 baseEnd_4777165 := by
    simpa [prefixWord, tailWord_4777165, baseEnd_4777165] using wordTrace_append hprefix tailTrace_4777165
  have hstable : (prefixWord ++ tailWord_4777165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777165).length < 2 ^ (prefixWord ++ tailWord_4777165).sum := by decide
  have hdescent : baseEnd_4777165 < baseStart_4777165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777184 : List Nat := [2, 1, 1, 3, 1, 4, 3, 2, 2, 2, 2]
def baseStart_4777184 : Nat := 118140960795 + 4777184 * 2 ^ 59
def prefixEnd_4777184 : Nat := 4983230072969 + 3 ^ 40 * 4777184 * 2
def baseEnd_4777184 : Nat := 2452991566968342479330137

theorem tailTrace_4777184 : CollatzResearch.WordTrace tailWord_4777184 prefixEnd_4777184 2452991566968342479330137 := by
  unfold tailWord_4777184
  simp only [CollatzResearch.WordTrace]
  refine ⟨87119107362542860458469303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116158809816723813944625737 87119107362542860458469303)
  ·
    refine ⟨130678661043814290687703955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87119107362542860458469303 130678661043814290687703955)
    ·
      refine ⟨196017991565721436031555933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130678661043814290687703955 196017991565721436031555933)
      ·
        refine ⟨73506746837145538511833475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196017991565721436031555933 73506746837145538511833475)
        ·
          refine ⟨110260120255718307767750213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73506746837145538511833475 110260120255718307767750213)
          ·
            refine ⟨20673772547947182706453165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110260120255718307767750213 20673772547947182706453165)
            ·
              refine ⟨7752664705480193514919937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20673772547947182706453165 7752664705480193514919937)
              ·
                refine ⟨5814498529110145136189953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7752664705480193514919937 5814498529110145136189953)
                ·
                  refine ⟨4360873896832608852142465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5814498529110145136189953 4360873896832608852142465)
                  ·
                    refine ⟨3270655422624456639106849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4360873896832608852142465 3270655422624456639106849)
                    ·
                      refine ⟨2452991566968342479330137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3270655422624456639106849 2452991566968342479330137)
                      ·
                        rfl

theorem cell23_4777184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 2, 2, 2, 2].length) (baseStart_4777184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777184 prefixEnd_4777184 := by exact prefixLift 4777184
  have htrace : WordTrace (prefixWord ++ tailWord_4777184) baseStart_4777184 baseEnd_4777184 := by
    simpa [prefixWord, tailWord_4777184, baseEnd_4777184] using wordTrace_append hprefix tailTrace_4777184
  have hstable : (prefixWord ++ tailWord_4777184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777184).length < 2 ^ (prefixWord ++ tailWord_4777184).sum := by decide
  have hdescent : baseEnd_4777184 < baseStart_4777184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777203 : List Nat := [1, 1, 1, 2, 2, 5, 1, 2, 1, 7]
def baseStart_4777203 : Nat := 118140960795 + 4777203 * 2 ^ 59
def prefixEnd_4777203 : Nat := 4983230072969 + 3 ^ 40 * 4777203 * 2
def baseEnd_4777203 : Nat := 817667107700259301664183

theorem tailTrace_4777203 : CollatzResearch.WordTrace tailWord_4777203 prefixEnd_4777203 817667107700259301664183 := by
  unfold tailWord_4777203
  simp only [CollatzResearch.WordTrace]
  refine ⟨174238907712016887161880263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116159271808011258107920175 174238907712016887161880263)
  ·
    refine ⟨261358361568025330742820395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174238907712016887161880263 261358361568025330742820395)
    ·
      refine ⟨392037542352037996114230593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261358361568025330742820395 392037542352037996114230593)
      ·
        refine ⟨294028156764028497085672945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 392037542352037996114230593 294028156764028497085672945)
        ·
          refine ⟨220521117573021372814254709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 294028156764028497085672945 220521117573021372814254709)
          ·
            refine ⟨20673854772470753701336379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 220521117573021372814254709 20673854772470753701336379)
            ·
              refine ⟨31010782158706130552004569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20673854772470753701336379 31010782158706130552004569)
              ·
                refine ⟨23258086619029597914003427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31010782158706130552004569 23258086619029597914003427)
                ·
                  refine ⟨34887129928544396871005141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23258086619029597914003427 34887129928544396871005141)
                  ·
                    refine ⟨817667107700259301664183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34887129928544396871005141 817667107700259301664183)
                    ·
                      rfl

theorem cell23_4777203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 7].length) (baseStart_4777203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777203 prefixEnd_4777203 := by exact prefixLift 4777203
  have htrace : WordTrace (prefixWord ++ tailWord_4777203) baseStart_4777203 baseEnd_4777203 := by
    simpa [prefixWord, tailWord_4777203, baseEnd_4777203] using wordTrace_append hprefix tailTrace_4777203
  have hstable : (prefixWord ++ tailWord_4777203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777203).length < 2 ^ (prefixWord ++ tailWord_4777203).sum := by decide
  have hdescent : baseEnd_4777203 < baseStart_4777203 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777213 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 5, 2, 5]
def baseStart_4777213 : Nat := 118140960795 + 4777213 * 2 ^ 59
def prefixEnd_4777213 : Nat := 4983230072969 + 3 ^ 40 * 4777213 * 2
def baseEnd_4777213 : Nat := 2453006457907322865867503

theorem tailTrace_4777213 : CollatzResearch.WordTrace tailWord_4777213 prefixEnd_4777213 2453006457907322865867503 := by
  unfold tailWord_4777213
  simp only [CollatzResearch.WordTrace]
  refine ⟨174239272441980658869744293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116159514961320439246496195 174239272441980658869744293)
  ·
    refine ⟨32669863582871373538077055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174239272441980658869744293 32669863582871373538077055)
    ·
      refine ⟨49004795374307060307115583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32669863582871373538077055 49004795374307060307115583)
      ·
        refine ⟨73507193061460590460673375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49004795374307060307115583 73507193061460590460673375)
        ·
          refine ⟨110260789592190885691010063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73507193061460590460673375 110260789592190885691010063)
          ·
            refine ⟨165391184388286328536515095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110260789592190885691010063 165391184388286328536515095)
            ·
              refine ⟨248086776582429492804772643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165391184388286328536515095 248086776582429492804772643)
              ·
                refine ⟨372130164873644239207158965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 248086776582429492804772643 372130164873644239207158965)
                ·
                  refine ⟨34887202956904147425671153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 372130164873644239207158965 34887202956904147425671153)
                  ·
                    refine ⟨26165402217678110569253365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34887202956904147425671153 26165402217678110569253365)
                    ·
                      refine ⟨2453006457907322865867503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26165402217678110569253365 2453006457907322865867503)
                      ·
                        rfl

theorem cell23_4777213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_4777213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777213 prefixEnd_4777213 := by exact prefixLift 4777213
  have htrace : WordTrace (prefixWord ++ tailWord_4777213) baseStart_4777213 baseEnd_4777213 := by
    simpa [prefixWord, tailWord_4777213, baseEnd_4777213] using wordTrace_append hprefix tailTrace_4777213
  have hstable : (prefixWord ++ tailWord_4777213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777213).length < 2 ^ (prefixWord ++ tailWord_4777213).sum := by decide
  have hdescent : baseEnd_4777213 < baseStart_4777213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777220 : List Nat := [2, 3, 2, 2, 2, 1, 2, 1, 1, 7]
def baseStart_4777220 : Nat := 118140960795 + 4777220 * 2 ^ 59
def prefixEnd_4777220 : Nat := 4983230072969 + 3 ^ 40 * 4777220 * 2
def baseEnd_4777220 : Nat := 817670017423968112826657

theorem tailTrace_4777220 : CollatzResearch.WordTrace tailWord_4777220 prefixEnd_4777220 817670017423968112826657 := by
  unfold tailWord_4777220
  simp only [CollatzResearch.WordTrace]
  refine ⟨87119763876477649532624557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116159685168636866043499409 87119763876477649532624557)
  ·
    refine ⟨32669911453679118574734209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87119763876477649532624557 32669911453679118574734209)
    ·
      refine ⟨24502433590259338931050657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32669911453679118574734209 24502433590259338931050657)
      ·
        refine ⟨18376825192694504198287993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24502433590259338931050657 18376825192694504198287993)
        ·
          refine ⟨13782618894520878148715995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18376825192694504198287993 13782618894520878148715995)
          ·
            refine ⟨20673928341781317223073993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13782618894520878148715995 20673928341781317223073993)
            ·
              refine ⟨15505446256335987917305495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20673928341781317223073993 15505446256335987917305495)
              ·
                refine ⟨23258169384503981875958243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15505446256335987917305495 23258169384503981875958243)
                ·
                  refine ⟨34887254076755972813937365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23258169384503981875958243 34887254076755972813937365)
                  ·
                    refine ⟨817670017423968112826657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34887254076755972813937365 817670017423968112826657)
                    ·
                      rfl

theorem cell23_4777220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_4777220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777220 prefixEnd_4777220 := by exact prefixLift 4777220
  have htrace : WordTrace (prefixWord ++ tailWord_4777220) baseStart_4777220 baseEnd_4777220 := by
    simpa [prefixWord, tailWord_4777220, baseEnd_4777220] using wordTrace_append hprefix tailTrace_4777220
  have hstable : (prefixWord ++ tailWord_4777220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777220).length < 2 ^ (prefixWord ++ tailWord_4777220).sum := by decide
  have hdescent : baseEnd_4777220 < baseStart_4777220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777224 : List Nat := [2, 1, 3, 2, 4, 2, 1, 3, 5]
def baseStart_4777224 : Nat := 118140960795 + 4777224 * 2 ^ 59
def prefixEnd_4777224 : Nat := 4983230072969 + 3 ^ 40 * 4777224 * 2
def baseEnd_4777224 : Nat := 272556900688280258092217

theorem tailTrace_4777224 : CollatzResearch.WordTrace tailWord_4777224 prefixEnd_4777224 272556900688280258092217 := by
  unfold tailWord_4777224
  simp only [CollatzResearch.WordTrace]
  refine ⟨87119836822470403874197363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116159782429960538498929817 87119836822470403874197363)
  ·
    refine ⟨130679755233705605811296045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87119836822470403874197363 130679755233705605811296045)
    ·
      refine ⟨49004908212639602179236017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130679755233705605811296045 49004908212639602179236017)
      ·
        refine ⟨36753681159479701634427013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49004908212639602179236017 36753681159479701634427013)
        ·
          refine ⟨6891315217402444056455065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36753681159479701634427013 6891315217402444056455065)
          ·
            refine ⟨5168486413051833042341299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6891315217402444056455065 5168486413051833042341299)
            ·
              refine ⟨7752729619577749563511949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5168486413051833042341299 7752729619577749563511949)
              ·
                refine ⟨2907273607341656086316981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7752729619577749563511949 2907273607341656086316981)
                ·
                  refine ⟨272556900688280258092217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2907273607341656086316981 272556900688280258092217)
                  ·
                    rfl

theorem cell23_4777224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 3, 5].length) (baseStart_4777224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777224 prefixEnd_4777224 := by exact prefixLift 4777224
  have htrace : WordTrace (prefixWord ++ tailWord_4777224) baseStart_4777224 baseEnd_4777224 := by
    simpa [prefixWord, tailWord_4777224, baseEnd_4777224] using wordTrace_append hprefix tailTrace_4777224
  have hstable : (prefixWord ++ tailWord_4777224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777224).length < 2 ^ (prefixWord ++ tailWord_4777224).sum := by decide
  have hdescent : baseEnd_4777224 < baseStart_4777224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777240 : List Nat := [2, 1, 2, 3, 1, 3, 1, 1, 4, 1, 4]
def baseStart_4777240 : Nat := 118140960795 + 4777240 * 2 ^ 59
def prefixEnd_4777240 : Nat := 4983230072969 + 3 ^ 40 * 4777240 * 2
def baseEnd_4777240 : Nat := 2453020321884994260229879

theorem tailTrace_4777240 : CollatzResearch.WordTrace tailWord_4777240 prefixEnd_4777240 2453020321884994260229879 := by
  unfold tailWord_4777240
  simp only [CollatzResearch.WordTrace]
  refine ⟨87120128606441421240488587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116160171475255228320651449 87120128606441421240488587)
  ·
    refine ⟨130680192909662131860732881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87120128606441421240488587 130680192909662131860732881)
    ·
      refine ⟨98010144682246598895549661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130680192909662131860732881 98010144682246598895549661)
      ·
        refine ⟨36753804255842474585831123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98010144682246598895549661 36753804255842474585831123)
        ·
          refine ⟨55130706383763711878746685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36753804255842474585831123 55130706383763711878746685)
          ·
            refine ⟨20674014893911391954530007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55130706383763711878746685 20674014893911391954530007)
            ·
              refine ⟨31011022340867087931795011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20674014893911391954530007 31011022340867087931795011)
              ·
                refine ⟨46516533511300631897692517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31011022340867087931795011 46516533511300631897692517)
                ·
                  refine ⟨8721850033368868480817347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46516533511300631897692517 8721850033368868480817347)
                  ·
                    refine ⟨13082775050053302721226021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8721850033368868480817347 13082775050053302721226021)
                    ·
                      refine ⟨2453020321884994260229879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13082775050053302721226021 2453020321884994260229879)
                      ·
                        rfl

theorem cell23_4777240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_4777240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777240 prefixEnd_4777240 := by exact prefixLift 4777240
  have htrace : WordTrace (prefixWord ++ tailWord_4777240) baseStart_4777240 baseEnd_4777240 := by
    simpa [prefixWord, tailWord_4777240, baseEnd_4777240] using wordTrace_append hprefix tailTrace_4777240
  have hstable : (prefixWord ++ tailWord_4777240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777240).length < 2 ^ (prefixWord ++ tailWord_4777240).sum := by decide
  have hdescent : baseEnd_4777240 < baseStart_4777240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777260 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 3]
def baseStart_4777260 : Nat := 118140960795 + 4777260 * 2 ^ 59
def prefixEnd_4777260 : Nat := 4983230072969 + 3 ^ 40 * 4777260 * 2
def baseEnd_4777260 : Nat := 2453030591498084181979787

theorem tailTrace_4777260 : CollatzResearch.WordTrace tailWord_4777260 prefixEnd_4777260 2453030591498084181979787 := by
  unfold tailWord_4777260
  simp only [CollatzResearch.WordTrace]
  refine ⟨87120493336405192948352617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116160657781873590597803489 87120493336405192948352617)
  ·
    refine ⟨65340370002303894711264463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87120493336405192948352617 65340370002303894711264463)
    ·
      refine ⟨98010555003455842066896695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65340370002303894711264463 98010555003455842066896695)
      ·
        refine ⟨147015832505183763100345043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98010555003455842066896695 147015832505183763100345043)
        ·
          refine ⟨220523748757775644650517565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147015832505183763100345043 220523748757775644650517565)
          ·
            refine ⟨82696405784165866743944087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 220523748757775644650517565 82696405784165866743944087)
            ·
              refine ⟨124044608676248800115916131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82696405784165866743944087 124044608676248800115916131)
              ·
                refine ⟨186066913014373200173874197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124044608676248800115916131 186066913014373200173874197)
                ·
                  refine ⟨8721886547548743758150353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 186066913014373200173874197 8721886547548743758150353)
                  ·
                    refine ⟨6541414910661557818612765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8721886547548743758150353 6541414910661557818612765)
                    ·
                      refine ⟨2453030591498084181979787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6541414910661557818612765 2453030591498084181979787)
                      ·
                        rfl

theorem cell23_4777260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 3].length) (baseStart_4777260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777260 prefixEnd_4777260 := by exact prefixLift 4777260
  have htrace : WordTrace (prefixWord ++ tailWord_4777260) baseStart_4777260 baseEnd_4777260 := by
    simpa [prefixWord, tailWord_4777260, baseEnd_4777260] using wordTrace_append hprefix tailTrace_4777260
  have hstable : (prefixWord ++ tailWord_4777260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777260).length < 2 ^ (prefixWord ++ tailWord_4777260).sum := by decide
  have hdescent : baseEnd_4777260 < baseStart_4777260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777283 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 8]
def baseStart_4777283 : Nat := 118140960795 + 4777283 * 2 ^ 59
def prefixEnd_4777283 : Nat := 4983230072969 + 3 ^ 40 * 4777283 * 2
def baseEnd_4777283 : Nat := 2453042401553137591992181

theorem tailTrace_4777283 : CollatzResearch.WordTrace tailWord_4777283 prefixEnd_4777283 2453042401553137591992181 := by
  unfold tailWord_4777283
  simp only [CollatzResearch.WordTrace]
  refine ⟨174241825551727060824792503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116161217034484707216528335 174241825551727060824792503)
  ·
    refine ⟨261362738327590591237188755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174241825551727060824792503 261362738327590591237188755)
    ·
      refine ⟨392044107491385886855783133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261362738327590591237188755 392044107491385886855783133)
      ·
        refine ⟨147016540309269707570918675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 392044107491385886855783133 147016540309269707570918675)
        ·
          refine ⟨220524810463904561356378013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147016540309269707570918675 220524810463904561356378013)
          ·
            refine ⟨82696803923964210508641755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 220524810463904561356378013 82696803923964210508641755)
            ·
              refine ⟨124045205885946315762962633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82696803923964210508641755 124045205885946315762962633)
              ·
                refine ⟨93033904414459736822221975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124045205885946315762962633 93033904414459736822221975)
                ·
                  refine ⟨139550856621689605233332963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93033904414459736822221975 139550856621689605233332963)
                  ·
                    refine ⟨209326284932534407849999445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 139550856621689605233332963 209326284932534407849999445)
                    ·
                      refine ⟨2453042401553137591992181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 209326284932534407849999445 2453042401553137591992181)
                      ·
                        rfl

theorem cell23_4777283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_4777283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777283 prefixEnd_4777283 := by exact prefixLift 4777283
  have htrace : WordTrace (prefixWord ++ tailWord_4777283) baseStart_4777283 baseEnd_4777283 := by
    simpa [prefixWord, tailWord_4777283, baseEnd_4777283] using wordTrace_append hprefix tailTrace_4777283
  have hstable : (prefixWord ++ tailWord_4777283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777283).length < 2 ^ (prefixWord ++ tailWord_4777283).sum := by decide
  have hdescent : baseEnd_4777283 < baseStart_4777283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777300 : List Nat := [2, 4, 1, 1, 2, 1, 2, 1, 1, 2, 6]
def baseStart_4777300 : Nat := 118140960795 + 4777300 * 2 ^ 59
def prefixEnd_4777300 : Nat := 4983230072969 + 3 ^ 40 * 4777300 * 2
def baseEnd_4777300 : Nat := 2453051130724264025479603

theorem tailTrace_4777300 : CollatzResearch.WordTrace tailWord_4777300 prefixEnd_4777300 2453051130724264025479603 := by
  unfold tailWord_4777300
  simp only [CollatzResearch.WordTrace]
  refine ⟨87121222796332736364080677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116161630395110315152107569 87121222796332736364080677)
  ·
    refine ⟨16335229274312388068265127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87121222796332736364080677 16335229274312388068265127)
    ·
      refine ⟨24502843911468582102397691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16335229274312388068265127 24502843911468582102397691)
      ·
        refine ⟨36754265867202873153596537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24502843911468582102397691 36754265867202873153596537)
        ·
          refine ⟨27565699400402154865197403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36754265867202873153596537 27565699400402154865197403)
          ·
            refine ⟨41348549100603232297796105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27565699400402154865197403 41348549100603232297796105)
            ·
              refine ⟨31011411825452424223347079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41348549100603232297796105 31011411825452424223347079)
              ·
                refine ⟨46517117738178636335020619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31011411825452424223347079 46517117738178636335020619)
                ·
                  refine ⟨69775676607267954502530929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46517117738178636335020619 69775676607267954502530929)
                  ·
                    refine ⟨52331757455450965876898197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 69775676607267954502530929 52331757455450965876898197)
                    ·
                      refine ⟨2453051130724264025479603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52331757455450965876898197 2453051130724264025479603)
                      ·
                        rfl

theorem cell23_4777300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_4777300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777300 prefixEnd_4777300 := by exact prefixLift 4777300
  have htrace : WordTrace (prefixWord ++ tailWord_4777300) baseStart_4777300 baseEnd_4777300 := by
    simpa [prefixWord, tailWord_4777300, baseEnd_4777300] using wordTrace_append hprefix tailTrace_4777300
  have hstable : (prefixWord ++ tailWord_4777300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777300).length < 2 ^ (prefixWord ++ tailWord_4777300).sum := by decide
  have hdescent : baseEnd_4777300 < baseStart_4777300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777301 : List Nat := [1, 3, 2, 2, 3, 1, 4, 2, 1, 4]
def baseStart_4777301 : Nat := 118140960795 + 4777301 * 2 ^ 59
def prefixEnd_4777301 : Nat := 4983230072969 + 3 ^ 40 * 4777301 * 2
def baseEnd_4777301 : Nat := 817683881401639507189033

theorem tailTrace_4777301 : CollatzResearch.WordTrace tailWord_4777301 prefixEnd_4777301 817683881401639507189033 := by
  unfold tailWord_4777301
  simp only [CollatzResearch.WordTrace]
  refine ⟨174242482065661849898947757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116161654710441233265965171 174242482065661849898947757)
  ·
    refine ⟨65340930774623193712105409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174242482065661849898947757 65340930774623193712105409)
    ·
      refine ⟨49005698080967395284079057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65340930774623193712105409 49005698080967395284079057)
      ·
        refine ⟨36754273560725546463059293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49005698080967395284079057 36754273560725546463059293)
        ·
          refine ⟨13782852585272079923647235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36754273560725546463059293 13782852585272079923647235)
          ·
            refine ⟨20674278877908119885470853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13782852585272079923647235 20674278877908119885470853)
            ·
              refine ⟨3876427289607772478525785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20674278877908119885470853 3876427289607772478525785)
              ·
                refine ⟨2907320467205829358894339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3876427289607772478525785 2907320467205829358894339)
                ·
                  refine ⟨4360980700808744038341509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2907320467205829358894339 4360980700808744038341509)
                  ·
                    refine ⟨817683881401639507189033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4360980700808744038341509 817683881401639507189033)
                    ·
                      rfl

theorem cell23_4777301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 2, 1, 4].length) (baseStart_4777301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777301 prefixEnd_4777301 := by exact prefixLift 4777301
  have htrace : WordTrace (prefixWord ++ tailWord_4777301) baseStart_4777301 baseEnd_4777301 := by
    simpa [prefixWord, tailWord_4777301, baseEnd_4777301] using wordTrace_append hprefix tailTrace_4777301
  have hstable : (prefixWord ++ tailWord_4777301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777301).length < 2 ^ (prefixWord ++ tailWord_4777301).sum := by decide
  have hdescent : baseEnd_4777301 < baseStart_4777301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777317 : List Nat := [1, 3, 1, 3, 1, 2, 2, 2, 1, 5, 2]
def baseStart_4777317 : Nat := 118140960795 + 4777317 * 2 ^ 59
def prefixEnd_4777317 : Nat := 4983230072969 + 3 ^ 40 * 4777317 * 2
def baseEnd_4777317 : Nat := 2453059859895390458967025

theorem tailTrace_4777317 : CollatzResearch.WordTrace tailWord_4777317 prefixEnd_4777317 2453059859895390458967025 := by
  unfold tailWord_4777317
  simp only [CollatzResearch.WordTrace]
  refine ⟨174243065633603884631530205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116162043755735923087686803 174243065633603884631530205)
  ·
    refine ⟨65341149612601456736823827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174243065633603884631530205 65341149612601456736823827)
    ·
      refine ⟨98011724418902185105235741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65341149612601456736823827 98011724418902185105235741)
      ·
        refine ⟨36754396657088319414463403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98011724418902185105235741 36754396657088319414463403)
        ·
          refine ⟨55131594985632479121695105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36754396657088319414463403 55131594985632479121695105)
          ·
            refine ⟨41348696239224359341271329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55131594985632479121695105 41348696239224359341271329)
            ·
              refine ⟨31011522179418269505953497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41348696239224359341271329 31011522179418269505953497)
              ·
                refine ⟨23258641634563702129465123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31011522179418269505953497 23258641634563702129465123)
                ·
                  refine ⟨34887962451845553194197685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23258641634563702129465123 34887962451845553194197685)
                  ·
                    refine ⟨3270746479860520611956033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34887962451845553194197685 3270746479860520611956033)
                    ·
                      refine ⟨2453059859895390458967025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3270746479860520611956033 2453059859895390458967025)
                      ·
                        rfl

theorem cell23_4777317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 5, 2].length) (baseStart_4777317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777317 prefixEnd_4777317 := by exact prefixLift 4777317
  have htrace : WordTrace (prefixWord ++ tailWord_4777317) baseStart_4777317 baseEnd_4777317 := by
    simpa [prefixWord, tailWord_4777317, baseEnd_4777317] using wordTrace_append hprefix tailTrace_4777317
  have hstable : (prefixWord ++ tailWord_4777317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777317).length < 2 ^ (prefixWord ++ tailWord_4777317).sum := by decide
  have hdescent : baseEnd_4777317 < baseStart_4777317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777324 : List Nat := [2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 3]
def baseStart_4777324 : Nat := 118140960795 + 4777324 * 2 ^ 59
def prefixEnd_4777324 : Nat := 4983230072969 + 3 ^ 40 * 4777324 * 2
def baseEnd_4777324 : Nat := 2453063454259971931579493

theorem tailTrace_4777324 : CollatzResearch.WordTrace tailWord_4777324 prefixEnd_4777324 2453063454259971931579493 := by
  unfold tailWord_4777324
  simp only [CollatzResearch.WordTrace]
  refine ⟨87121660472289262413517513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116162213963052349884690017 87121660472289262413517513)
  ·
    refine ⟨65341245354216946810138135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87121660472289262413517513 65341245354216946810138135)
    ·
      refine ⟨98011868031325420215207203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65341245354216946810138135 98011868031325420215207203)
      ·
        refine ⟨147017802046988130322810805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98011868031325420215207203 147017802046988130322810805)
        ·
          refine ⟨13782918941905137217763513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 147017802046988130322810805 13782918941905137217763513)
          ·
            refine ⟨10337189206428852913322635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13782918941905137217763513 10337189206428852913322635)
            ·
              refine ⟨15505783809643279369983953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10337189206428852913322635 15505783809643279369983953)
              ·
                refine ⟨11629337857232459527487965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15505783809643279369983953 11629337857232459527487965)
                ·
                  refine ⟨4361001696462172322807987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11629337857232459527487965 4361001696462172322807987)
                  ·
                    refine ⟨6541502544693258484211981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4361001696462172322807987 6541502544693258484211981)
                    ·
                      refine ⟨2453063454259971931579493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6541502544693258484211981 2453063454259971931579493)
                      ·
                        rfl

theorem cell23_4777324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 3].length) (baseStart_4777324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777324 prefixEnd_4777324 := by exact prefixLift 4777324
  have htrace : WordTrace (prefixWord ++ tailWord_4777324) baseStart_4777324 baseEnd_4777324 := by
    simpa [prefixWord, tailWord_4777324, baseEnd_4777324] using wordTrace_append hprefix tailTrace_4777324
  have hstable : (prefixWord ++ tailWord_4777324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777324).length < 2 ^ (prefixWord ++ tailWord_4777324).sum := by decide
  have hdescent : baseEnd_4777324 < baseStart_4777324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777340 : List Nat := [2, 2, 2, 1, 1, 1, 3, 4, 1, 6]
def baseStart_4777340 : Nat := 118140960795 + 4777340 * 2 ^ 59
def prefixEnd_4777340 : Nat := 4983230072969 + 3 ^ 40 * 4777340 * 2
def baseEnd_4777340 : Nat := 817690556650147956326473

theorem tailTrace_4777340 : CollatzResearch.WordTrace tailWord_4777340 prefixEnd_4777340 817690556650147956326473 := by
  unfold tailWord_4777340
  simp only [CollatzResearch.WordTrace]
  refine ⟨87121952256260279779808737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116162603008347039706411649 87121952256260279779808737)
  ·
    refine ⟨65341464192195209834856553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87121952256260279779808737 65341464192195209834856553)
    ·
      refine ⟨49006098144146407376142415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65341464192195209834856553 49006098144146407376142415)
      ·
        refine ⟨73509147216219611064213623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49006098144146407376142415 73509147216219611064213623)
        ·
          refine ⟨110263720824329416596320435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73509147216219611064213623 110263720824329416596320435)
          ·
            refine ⟨165395581236494124894480653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110263720824329416596320435 165395581236494124894480653)
            ·
              refine ⟨62023342963685296835430245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 165395581236494124894480653 62023342963685296835430245)
              ·
                refine ⟨11629376805690993156643171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62023342963685296835430245 11629376805690993156643171)
                ·
                  refine ⟨17444065208536489734964757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11629376805690993156643171 17444065208536489734964757)
                  ·
                    refine ⟨817690556650147956326473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17444065208536489734964757 817690556650147956326473)
                    ·
                      rfl

theorem cell23_4777340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_4777340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777340 prefixEnd_4777340 := by exact prefixLift 4777340
  have htrace : WordTrace (prefixWord ++ tailWord_4777340) baseStart_4777340 baseEnd_4777340 := by
    simpa [prefixWord, tailWord_4777340, baseEnd_4777340] using wordTrace_append hprefix tailTrace_4777340
  have hstable : (prefixWord ++ tailWord_4777340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777340).length < 2 ^ (prefixWord ++ tailWord_4777340).sum := by decide
  have hdescent : baseEnd_4777340 < baseStart_4777340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777341 : List Nat := [1, 4, 1, 1, 2, 2, 4, 3, 1, 1, 3]
def baseStart_4777341 : Nat := 118140960795 + 4777341 * 2 ^ 59
def prefixEnd_4777341 : Nat := 4983230072969 + 3 ^ 40 * 4777341 * 2
def baseEnd_4777341 : Nat := 2453072183431098365066915

theorem tailTrace_4777341 : CollatzResearch.WordTrace tailWord_4777341 prefixEnd_4777341 2453072183431098365066915 := by
  unfold tailWord_4777341
  simp only [CollatzResearch.WordTrace]
  refine ⟨174243940985516936730403877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116162627323677957820269251 174243940985516936730403877)
  ·
    refine ⟨32670738934784425636950727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174243940985516936730403877 32670738934784425636950727)
    ·
      refine ⟨49006108402176638455426091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32670738934784425636950727 49006108402176638455426091)
      ·
        refine ⟨73509162603264957683139137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49006108402176638455426091 73509162603264957683139137)
        ·
          refine ⟨55131871952448718262354353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73509162603264957683139137 55131871952448718262354353)
          ·
            refine ⟨41348903964336538696765765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55131871952448718262354353 41348903964336538696765765)
            ·
              refine ⟨7752919493313101005643581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41348903964336538696765765 7752919493313101005643581)
              ·
                refine ⟨2907344809992412877116343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7752919493313101005643581 2907344809992412877116343)
                ·
                  refine ⟨4361017214988619315674515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2907344809992412877116343 4361017214988619315674515)
                  ·
                    refine ⟨6541525822482928973511773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4361017214988619315674515 6541525822482928973511773)
                    ·
                      refine ⟨2453072183431098365066915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6541525822482928973511773 2453072183431098365066915)
                      ·
                        rfl

theorem cell23_4777341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 3, 1, 1, 3].length) (baseStart_4777341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777341 prefixEnd_4777341 := by exact prefixLift 4777341
  have htrace : WordTrace (prefixWord ++ tailWord_4777341) baseStart_4777341 baseEnd_4777341 := by
    simpa [prefixWord, tailWord_4777341, baseEnd_4777341] using wordTrace_append hprefix tailTrace_4777341
  have hstable : (prefixWord ++ tailWord_4777341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777341).length < 2 ^ (prefixWord ++ tailWord_4777341).sum := by decide
  have hdescent : baseEnd_4777341 < baseStart_4777341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777370 : List Nat := [3, 1, 1, 4, 1, 1, 2, 10]
def baseStart_4777370 : Nat := 118140960795 + 4777370 * 2 ^ 59
def prefixEnd_4777370 : Nat := 4983230072969 + 3 ^ 40 * 4777370 * 2
def baseEnd_4777370 : Nat := 90855076828521435244603

theorem tailTrace_4777370 : CollatzResearch.WordTrace tailWord_4777370 prefixEnd_4777370 90855076828521435244603 := by
  unfold tailWord_4777370
  simp only [CollatzResearch.WordTrace]
  refine ⟨43561249675602968670802391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116163332468274583122139709 43561249675602968670802391)
  ·
    refine ⟨65341874513404453006203587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43561249675602968670802391 65341874513404453006203587)
    ·
      refine ⟨98012811770106679509305381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65341874513404453006203587 98012811770106679509305381)
      ·
        refine ⟨18377402206895002407994759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98012811770106679509305381 18377402206895002407994759)
        ·
          refine ⟨27566103310342503611992139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18377402206895002407994759 27566103310342503611992139)
          ·
            refine ⟨41349154965513755417988209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27566103310342503611992139 41349154965513755417988209)
            ·
              refine ⟨31011866224135316563491157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41349154965513755417988209 31011866224135316563491157)
              ·
                refine ⟨90855076828521435244603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 31011866224135316563491157 90855076828521435244603)
                ·
                  rfl

theorem cell23_4777370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 10].length) (baseStart_4777370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777370 prefixEnd_4777370 := by exact prefixLift 4777370
  have htrace : WordTrace (prefixWord ++ tailWord_4777370) baseStart_4777370 baseEnd_4777370 := by
    simpa [prefixWord, tailWord_4777370, baseEnd_4777370] using wordTrace_append hprefix tailTrace_4777370
  have hstable : (prefixWord ++ tailWord_4777370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777370).length < 2 ^ (prefixWord ++ tailWord_4777370).sum := by decide
  have hdescent : baseEnd_4777370 < baseStart_4777370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777404 : List Nat := [2, 2, 2, 4, 3, 1, 9]
def baseStart_4777404 : Nat := 118140960795 + 4777404 * 2 ^ 59
def prefixEnd_4777404 : Nat := 4983230072969 + 3 ^ 40 * 4777404 * 2
def baseEnd_4777404 : Nat := 30285241144596686649125

theorem tailTrace_4777404 : CollatzResearch.WordTrace tailWord_4777404 prefixEnd_4777404 30285241144596686649125 := by
  unfold tailWord_4777404
  simp only [CollatzResearch.WordTrace]
  refine ⟨87123119392144349244973633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116164159189525798993298177 87123119392144349244973633)
  ·
    refine ⟨65342339544108261933730225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87123119392144349244973633 65342339544108261933730225)
    ·
      refine ⟨49006754658081196450297669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65342339544108261933730225 49006754658081196450297669)
      ·
        refine ⟨9188766498390224334430813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49006754658081196450297669 9188766498390224334430813)
        ·
          refine ⟨3445787436896334125411555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9188766498390224334430813 3445787436896334125411555)
          ·
            refine ⟨5168681155344501188117333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3445787436896334125411555 5168681155344501188117333)
            ·
              refine ⟨30285241144596686649125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5168681155344501188117333 30285241144596686649125)
              ·
                rfl

theorem cell23_4777404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 9].length) (baseStart_4777404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777404 prefixEnd_4777404 := by exact prefixLift 4777404
  have htrace : WordTrace (prefixWord ++ tailWord_4777404) baseStart_4777404 baseEnd_4777404 := by
    simpa [prefixWord, tailWord_4777404, baseEnd_4777404] using wordTrace_append hprefix tailTrace_4777404
  have hstable : (prefixWord ++ tailWord_4777404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777404).length < 2 ^ (prefixWord ++ tailWord_4777404).sum := by decide
  have hdescent : baseEnd_4777404 < baseStart_4777404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777441 : List Nat := [1, 2, 3, 1, 2, 3, 3, 2, 1, 3, 2]
def baseStart_4777441 : Nat := 118140960795 + 4777441 * 2 ^ 59
def prefixEnd_4777441 : Nat := 4983230072969 + 3 ^ 40 * 4777441 * 2
def baseEnd_4777441 : Nat := 2453123531496547973816455

theorem tailTrace_4777441 : CollatzResearch.WordTrace tailWord_4777441 prefixEnd_4777441 2453123531496547973816455 := by
  unfold tailWord_4777441
  simp only [CollatzResearch.WordTrace]
  refine ⟨174247588285154653809044177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116165058856769769206029451 174247588285154653809044177)
  ·
    refine ⟨130685691213865990356783133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174247588285154653809044177 130685691213865990356783133)
    ·
      refine ⟨49007134205199746383793675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130685691213865990356783133 49007134205199746383793675)
      ·
        refine ⟨73510701307799619575690513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49007134205199746383793675 73510701307799619575690513)
        ·
          refine ⟨55133025980849714681767885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73510701307799619575690513 55133025980849714681767885)
          ·
            refine ⟨20674884742818643005662957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55133025980849714681767885 20674884742818643005662957)
            ·
              refine ⟨7753081778556991127123609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20674884742818643005662957 7753081778556991127123609)
              ·
                refine ⟨5814811333917743345342707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7753081778556991127123609 5814811333917743345342707)
                ·
                  refine ⟨8722217000876615018014061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5814811333917743345342707 8722217000876615018014061)
                  ·
                    refine ⟨3270831375328730631755273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8722217000876615018014061 3270831375328730631755273)
                    ·
                      refine ⟨2453123531496547973816455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3270831375328730631755273 2453123531496547973816455)
                      ·
                        rfl

theorem cell23_4777441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2, 1, 3, 2].length) (baseStart_4777441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777441 prefixEnd_4777441 := by exact prefixLift 4777441
  have htrace : WordTrace (prefixWord ++ tailWord_4777441) baseStart_4777441 baseEnd_4777441 := by
    simpa [prefixWord, tailWord_4777441, baseEnd_4777441] using wordTrace_append hprefix tailTrace_4777441
  have hstable : (prefixWord ++ tailWord_4777441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777441).length < 2 ^ (prefixWord ++ tailWord_4777441).sum := by decide
  have hdescent : baseEnd_4777441 < baseStart_4777441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777457 : List Nat := [1, 2, 2, 2, 3, 2, 2, 1, 2, 1, 5]
def baseStart_4777457 : Nat := 118140960795 + 4777457 * 2 ^ 59
def prefixEnd_4777457 : Nat := 4983230072969 + 3 ^ 40 * 4777457 * 2
def baseEnd_4777457 : Nat := 2453131747187019911216381

theorem tailTrace_4777457 : CollatzResearch.WordTrace tailWord_4777457 prefixEnd_4777457 2453131747187019911216381 := by
  unfold tailWord_4777457
  simp only [CollatzResearch.WordTrace]
  refine ⟨174248171853096688541626625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116165447902064459027751083 174248171853096688541626625)
  ·
    refine ⟨130686128889822516406219969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174248171853096688541626625 130686128889822516406219969)
    ·
      refine ⟨98014596667366887304664977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130686128889822516406219969 98014596667366887304664977)
      ·
        refine ⟨73510947500525165478498733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98014596667366887304664977 73510947500525165478498733)
        ·
          refine ⟨27566605312696937054437025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73510947500525165478498733 27566605312696937054437025)
          ·
            refine ⟨20674953984522702790827769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27566605312696937054437025 20674953984522702790827769)
            ·
              refine ⟨15506215488392027093120827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20674953984522702790827769 15506215488392027093120827)
              ·
                refine ⟨23259323232588040639681241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15506215488392027093120827 23259323232588040639681241)
                ·
                  refine ⟨17444492424441030479760931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23259323232588040639681241 17444492424441030479760931)
                  ·
                    refine ⟨26166738636661545719641397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17444492424441030479760931 26166738636661545719641397)
                    ·
                      refine ⟨2453131747187019911216381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26166738636661545719641397 2453131747187019911216381)
                      ·
                        rfl

theorem cell23_4777457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_4777457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777457 prefixEnd_4777457 := by exact prefixLift 4777457
  have htrace : WordTrace (prefixWord ++ tailWord_4777457) baseStart_4777457 baseEnd_4777457 := by
    simpa [prefixWord, tailWord_4777457, baseEnd_4777457] using wordTrace_append hprefix tailTrace_4777457
  have hstable : (prefixWord ++ tailWord_4777457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777457).length < 2 ^ (prefixWord ++ tailWord_4777457).sum := by decide
  have hdescent : baseEnd_4777457 < baseStart_4777457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777484 : List Nat := [2, 2, 1, 2, 5, 1, 1, 1, 2, 2, 4]
def baseStart_4777484 : Nat := 118140960795 + 4777484 * 2 ^ 59
def prefixEnd_4777484 : Nat := 4983230072969 + 3 ^ 40 * 4777484 * 2
def baseEnd_4777484 : Nat := 2453145611164691305578757

theorem tailTrace_4777484 : CollatzResearch.WordTrace tailWord_4777484 prefixEnd_4777484 2453145611164691305578757 := by
  unfold tailWord_4777484
  simp only [CollatzResearch.WordTrace]
  refine ⟨87124578311999436076429753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116166104415999248101906337 87124578311999436076429753)
  ·
    refine ⟨65343433733999577057322315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87124578311999436076429753 65343433733999577057322315)
    ·
      refine ⟨98015150600999365585983473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65343433733999577057322315 98015150600999365585983473)
      ·
        refine ⟨73511362950749524189487605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98015150600999365585983473 73511362950749524189487605)
        ·
          refine ⟨6891690276632767892764463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73511362950749524189487605 6891690276632767892764463)
          ·
            refine ⟨10337535414949151839146695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6891690276632767892764463 10337535414949151839146695)
            ·
              refine ⟨15506303122423727758720043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10337535414949151839146695 15506303122423727758720043)
              ·
                refine ⟨23259454683635591638080065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15506303122423727758720043 23259454683635591638080065)
                ·
                  refine ⟨17444591012726693728560049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23259454683635591638080065 17444591012726693728560049)
                  ·
                    refine ⟨13083443259545020296420037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17444591012726693728560049 13083443259545020296420037)
                    ·
                      refine ⟨2453145611164691305578757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13083443259545020296420037 2453145611164691305578757)
                      ·
                        rfl

theorem cell23_4777484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 2, 2, 4].length) (baseStart_4777484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777484 prefixEnd_4777484 := by exact prefixLift 4777484
  have htrace : WordTrace (prefixWord ++ tailWord_4777484) baseStart_4777484 baseEnd_4777484 := by
    simpa [prefixWord, tailWord_4777484, baseEnd_4777484] using wordTrace_append hprefix tailTrace_4777484
  have hstable : (prefixWord ++ tailWord_4777484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777484).length < 2 ^ (prefixWord ++ tailWord_4777484).sum := by decide
  have hdescent : baseEnd_4777484 < baseStart_4777484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777557 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 1, 6, 4]
def baseStart_4777557 : Nat := 118140960795 + 4777557 * 2 ^ 59
def prefixEnd_4777557 : Nat := 4983230072969 + 3 ^ 40 * 4777557 * 2
def baseEnd_4777557 : Nat := 2453183095252469519965921

theorem tailTrace_4777557 : CollatzResearch.WordTrace tailWord_4777557 prefixEnd_4777557 2453183095252469519965921 := by
  unfold tailWord_4777557
  simp only [CollatzResearch.WordTrace]
  refine ⟨174251819152734405620266925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116167879435156270413511283 174251819152734405620266925)
  ·
    refine ⟨65344432182275402107600097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174251819152734405620266925 65344432182275402107600097)
    ·
      refine ⟨49008324136706551580700073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65344432182275402107600097 49008324136706551580700073)
      ·
        refine ⟨36756243102529913685525055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49008324136706551580700073 36756243102529913685525055)
        ·
          refine ⟨55134364653794870528287583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36756243102529913685525055 55134364653794870528287583)
          ·
            refine ⟨82701546980692305792431375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55134364653794870528287583 82701546980692305792431375)
            ·
              refine ⟨124052320471038458688647063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82701546980692305792431375 124052320471038458688647063)
              ·
                refine ⟨186078480706557688032970595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124052320471038458688647063 186078480706557688032970595)
                ·
                  refine ⟨279117721059836532049455893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 186078480706557688032970595 279117721059836532049455893)
                  ·
                    refine ⟨13083643174679837439818245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 279117721059836532049455893 13083643174679837439818245)
                    ·
                      refine ⟨2453183095252469519965921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13083643174679837439818245 2453183095252469519965921)
                      ·
                        rfl

theorem cell23_4777557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_4777557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777557 prefixEnd_4777557 := by exact prefixLift 4777557
  have htrace : WordTrace (prefixWord ++ tailWord_4777557) baseStart_4777557 baseEnd_4777557 := by
    simpa [prefixWord, tailWord_4777557, baseEnd_4777557] using wordTrace_append hprefix tailTrace_4777557
  have hstable : (prefixWord ++ tailWord_4777557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777557).length < 2 ^ (prefixWord ++ tailWord_4777557).sum := by decide
  have hdescent : baseEnd_4777557 < baseStart_4777557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777601 : List Nat := [1, 2, 4, 2, 1, 2, 4, 1, 6]
def baseStart_4777601 : Nat := 118140960795 + 4777601 * 2 ^ 59
def prefixEnd_4777601 : Nat := 4983230072969 + 3 ^ 40 * 4777601 * 2
def baseEnd_4777601 : Nat := 272578409822363038646191

theorem tailTrace_4777601 : CollatzResearch.WordTrace tailWord_4777601 prefixEnd_4777601 272578409822363038646191 := by
  unfold tailWord_4777601
  simp only [CollatzResearch.WordTrace]
  refine ⟨174253423964575001134868657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116168949309716667423245771 174253423964575001134868657)
  ·
    refine ⟨130690067973431250851151493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174253423964575001134868657 130690067973431250851151493)
    ·
      refine ⟨24504387745018359534590905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130690067973431250851151493 24504387745018359534590905)
      ·
        refine ⟨18378290808763769650943179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24504387745018359534590905 18378290808763769650943179)
        ·
          refine ⟨27567436213145654476414769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18378290808763769650943179 27567436213145654476414769)
          ·
            refine ⟨20675577159859240857311077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27567436213145654476414769 20675577159859240857311077)
            ·
              refine ⟨3876670717473607660745827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20675577159859240857311077 3876670717473607660745827)
              ·
                refine ⟨5815006076210411491118741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3876670717473607660745827 5815006076210411491118741)
                ·
                  refine ⟨272578409822363038646191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5815006076210411491118741 272578409822363038646191)
                  ·
                    rfl

theorem cell23_4777601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 1, 6].length) (baseStart_4777601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777601 prefixEnd_4777601 := by exact prefixLift 4777601
  have htrace : WordTrace (prefixWord ++ tailWord_4777601) baseStart_4777601 baseEnd_4777601 := by
    simpa [prefixWord, tailWord_4777601, baseEnd_4777601] using wordTrace_append hprefix tailTrace_4777601
  have hstable : (prefixWord ++ tailWord_4777601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777601).length < 2 ^ (prefixWord ++ tailWord_4777601).sum := by decide
  have hdescent : baseEnd_4777601 < baseStart_4777601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777645 : List Nat := [1, 5, 2, 1, 1, 1, 3, 4, 1, 1, 3]
def baseStart_4777645 : Nat := 118140960795 + 4777645 * 2 ^ 59
def prefixEnd_4777645 : Nat := 4983230072969 + 3 ^ 40 * 4777645 * 2
def baseEnd_4777645 : Nat := 2453228281550065175665517

theorem tailTrace_4777645 : CollatzResearch.WordTrace tailWord_4777645 prefixEnd_4777645 2453228281550065175665517 := by
  unfold tailWord_4777645
  simp only [CollatzResearch.WordTrace]
  refine ⟨174255028776415596649470389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116170019184277064432980259 174255028776415596649470389)
  ·
    refine ⟨16336408947788962185887849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 174255028776415596649470389 16336408947788962185887849)
    ·
      refine ⟨12252306710841721639415887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16336408947788962185887849 12252306710841721639415887)
      ·
        refine ⟨18378460066262582459123831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12252306710841721639415887 18378460066262582459123831)
        ·
          refine ⟨27567690099393873688685747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18378460066262582459123831 27567690099393873688685747)
          ·
            refine ⟨41351535149090810533028621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27567690099393873688685747 41351535149090810533028621)
            ·
              refine ⟨15506825680909053949885733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41351535149090810533028621 15506825680909053949885733)
              ·
                refine ⟨2907529815170447615603575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15506825680909053949885733 2907529815170447615603575)
                ·
                  refine ⟨4361294722755671423405363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2907529815170447615603575 4361294722755671423405363)
                  ·
                    refine ⟨6541942084133507135108045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4361294722755671423405363 6541942084133507135108045)
                    ·
                      refine ⟨2453228281550065175665517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6541942084133507135108045 2453228281550065175665517)
                      ·
                        rfl

theorem cell23_4777645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_4777645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777645 prefixEnd_4777645 := by exact prefixLift 4777645
  have htrace : WordTrace (prefixWord ++ tailWord_4777645) baseStart_4777645 baseEnd_4777645 := by
    simpa [prefixWord, tailWord_4777645, baseEnd_4777645] using wordTrace_append hprefix tailTrace_4777645
  have hstable : (prefixWord ++ tailWord_4777645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777645).length < 2 ^ (prefixWord ++ tailWord_4777645).sum := by decide
  have hdescent : baseEnd_4777645 < baseStart_4777645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777661 : List Nat := [1, 4, 1, 2, 1, 2, 1, 5, 2, 4]
def baseStart_4777661 : Nat := 118140960795 + 4777661 * 2 ^ 59
def prefixEnd_4777661 : Nat := 4983230072969 + 3 ^ 40 * 4777661 * 2
def baseEnd_4777661 : Nat := 817745499080179037688481

theorem tailTrace_4777661 : CollatzResearch.WordTrace tailWord_4777661 prefixEnd_4777661 817745499080179037688481 := by
  unfold tailWord_4777661
  simp only [CollatzResearch.WordTrace]
  refine ⟨174255612344357631382052837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116170408229571754254701891 174255612344357631382052837)
  ·
    refine ⟨32672927314567055884134907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174255612344357631382052837 32672927314567055884134907)
    ·
      refine ⟨49009390971850583826202361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32672927314567055884134907 49009390971850583826202361)
      ·
        refine ⟨36757043228887937869651771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49009390971850583826202361 36757043228887937869651771)
        ·
          refine ⟨55135564843331906804477657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36757043228887937869651771 55135564843331906804477657)
          ·
            refine ⟨41351673632498930103358243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55135564843331906804477657 41351673632498930103358243)
            ·
              refine ⟨62027510448748395155037365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41351673632498930103358243 62027510448748395155037365)
              ·
                refine ⟨5815079104570162045784753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62027510448748395155037365 5815079104570162045784753)
                ·
                  refine ⟨4361309328427621534338565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5815079104570162045784753 4361309328427621534338565)
                  ·
                    refine ⟨817745499080179037688481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4361309328427621534338565 817745499080179037688481)
                    ·
                      rfl

theorem cell23_4777661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 5, 2, 4].length) (baseStart_4777661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777661 prefixEnd_4777661 := by exact prefixLift 4777661
  have htrace : WordTrace (prefixWord ++ tailWord_4777661) baseStart_4777661 baseEnd_4777661 := by
    simpa [prefixWord, tailWord_4777661, baseEnd_4777661] using wordTrace_append hprefix tailTrace_4777661
  have hstable : (prefixWord ++ tailWord_4777661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777661).length < 2 ^ (prefixWord ++ tailWord_4777661).sum := by decide
  have hdescent : baseEnd_4777661 < baseStart_4777661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777667 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 7]
def baseStart_4777667 : Nat := 118140960795 + 4777667 * 2 ^ 59
def prefixEnd_4777667 : Nat := 4983230072969 + 3 ^ 40 * 4777667 * 2
def baseEnd_4777667 : Nat := 2453239578124464089590415

theorem tailTrace_4777667 : CollatzResearch.WordTrace tailWord_4777667 prefixEnd_4777667 2453239578124464089590415 := by
  unfold tailWord_4777667
  simp only [CollatzResearch.WordTrace]
  refine ⟨174255831182335894406771255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116170554121557262937847503 174255831182335894406771255)
  ·
    refine ⟨261383746773503841610156883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174255831182335894406771255 261383746773503841610156883)
    ·
      refine ⟨392075620160255762415235325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261383746773503841610156883 392075620160255762415235325)
      ·
        refine ⟨147028357560095910905713247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 392075620160255762415235325 147028357560095910905713247)
        ·
          refine ⟨220542536340143866358569871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147028357560095910905713247 220542536340143866358569871)
          ·
            refine ⟨330813804510215799537854807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220542536340143866358569871 330813804510215799537854807)
            ·
              refine ⟨496220706765323699306782211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 330813804510215799537854807 496220706765323699306782211)
              ·
                refine ⟨744331060147985548960173317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 496220706765323699306782211 744331060147985548960173317)
                ·
                  refine ⟨139562073777747290430032497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 744331060147985548960173317 139562073777747290430032497)
                  ·
                    refine ⟨104671555333310467822524373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 139562073777747290430032497 104671555333310467822524373)
                    ·
                      refine ⟨2453239578124464089590415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 104671555333310467822524373 2453239578124464089590415)
                      ·
                        rfl

theorem cell23_4777667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_4777667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777667 prefixEnd_4777667 := by exact prefixLift 4777667
  have htrace : WordTrace (prefixWord ++ tailWord_4777667) baseStart_4777667 baseEnd_4777667 := by
    simpa [prefixWord, tailWord_4777667, baseEnd_4777667] using wordTrace_append hprefix tailTrace_4777667
  have hstable : (prefixWord ++ tailWord_4777667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777667).length < 2 ^ (prefixWord ++ tailWord_4777667).sum := by decide
  have hdescent : baseEnd_4777667 < baseStart_4777667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777671 : List Nat := [1, 1, 4, 1, 1, 1, 4, 4, 1, 2, 3]
def baseStart_4777671 : Nat := 118140960795 + 4777671 * 2 ^ 59
def prefixEnd_4777671 : Nat := 4983230072969 + 3 ^ 40 * 4777671 * 2
def baseEnd_4777671 : Nat := 2453241632047082073940397

theorem tailTrace_4777671 : CollatzResearch.WordTrace tailWord_4777671 prefixEnd_4777671 2453241632047082073940397 := by
  unfold tailWord_4777671
  simp only [CollatzResearch.WordTrace]
  refine ⟨174255977074321403089916867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116170651382880935393277911 174255977074321403089916867)
  ·
    refine ⟨261383965611482104634875301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174255977074321403089916867 261383965611482104634875301)
    ·
      refine ⟨49009493552152894619039119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 261383965611482104634875301 49009493552152894619039119)
      ·
        refine ⟨73514240328229341928558679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49009493552152894619039119 73514240328229341928558679)
        ·
          refine ⟨110271360492344012892838019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73514240328229341928558679 110271360492344012892838019)
          ·
            refine ⟨165407040738516019339257029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110271360492344012892838019 165407040738516019339257029)
            ·
              refine ⟨31013820138471753626110693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 165407040738516019339257029 31013820138471753626110693)
              ·
                refine ⟨5815091275963453804895755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31013820138471753626110693 5815091275963453804895755)
                ·
                  refine ⟨8722636913945180707343633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5815091275963453804895755 8722636913945180707343633)
                  ·
                    refine ⟨6541977685458885530507725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8722636913945180707343633 6541977685458885530507725)
                    ·
                      refine ⟨2453241632047082073940397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6541977685458885530507725 2453241632047082073940397)
                      ·
                        rfl

theorem cell23_4777671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 4, 1, 2, 3].length) (baseStart_4777671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777671 prefixEnd_4777671 := by exact prefixLift 4777671
  have htrace : WordTrace (prefixWord ++ tailWord_4777671) baseStart_4777671 baseEnd_4777671 := by
    simpa [prefixWord, tailWord_4777671, baseEnd_4777671] using wordTrace_append hprefix tailTrace_4777671
  have hstable : (prefixWord ++ tailWord_4777671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777671).length < 2 ^ (prefixWord ++ tailWord_4777671).sum := by decide
  have hdescent : baseEnd_4777671 < baseStart_4777671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777718 : List Nat := [5, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3]
def baseStart_4777718 : Nat := 118140960795 + 4777718 * 2 ^ 59
def prefixEnd_4777718 : Nat := 4983230072969 + 3 ^ 40 * 4777718 * 2
def baseEnd_4777718 : Nat := 2453265765637843390052681

theorem tailTrace_4777718 : CollatzResearch.WordTrace tailWord_4777718 prefixEnd_4777718 2453265765637843390052681 := by
  unfold tailWord_4777718
  simp only [CollatzResearch.WordTrace]
  refine ⟨10891105706571945632304863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116171794203434086744585205 10891105706571945632304863)
  ·
    refine ⟨16336658559857918448457295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10891105706571945632304863 16336658559857918448457295)
    ·
      refine ⟨24504987839786877672685943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16336658559857918448457295 24504987839786877672685943)
      ·
        refine ⟨36757481759680316509028915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24504987839786877672685943 36757481759680316509028915)
        ·
          refine ⟨55136222639520474763543373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36757481759680316509028915 55136222639520474763543373)
          ·
            refine ⟨20676083489820178036328765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55136222639520474763543373 20676083489820178036328765)
            ·
              refine ⟨7753531308682566763623287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20676083489820178036328765 7753531308682566763623287)
              ·
                refine ⟨11630296963023850145434931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7753531308682566763623287 11630296963023850145434931)
                ·
                  refine ⟨17445445444535775218152397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11630296963023850145434931 17445445444535775218152397)
                  ·
                    refine ⟨6542042041700915706807149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17445445444535775218152397 6542042041700915706807149)
                    ·
                      refine ⟨2453265765637843390052681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6542042041700915706807149 2453265765637843390052681)
                      ·
                        rfl

theorem cell23_4777718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_4777718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777718 prefixEnd_4777718 := by exact prefixLift 4777718
  have htrace : WordTrace (prefixWord ++ tailWord_4777718) baseStart_4777718 baseEnd_4777718 := by
    simpa [prefixWord, tailWord_4777718, baseEnd_4777718] using wordTrace_append hprefix tailTrace_4777718
  have hstable : (prefixWord ++ tailWord_4777718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777718).length < 2 ^ (prefixWord ++ tailWord_4777718).sum := by decide
  have hdescent : baseEnd_4777718 < baseStart_4777718 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777831 : List Nat := [1, 1, 5, 1, 2, 1, 2, 2, 1, 3, 4]
def baseStart_4777831 : Nat := 118140960795 + 4777831 * 2 ^ 59
def prefixEnd_4777831 : Nat := 4983230072969 + 3 ^ 40 * 4777831 * 2
def baseEnd_4777831 : Nat := 2453323788951801447939661

theorem tailTrace_4777831 : CollatzResearch.WordTrace tailWord_4777831 prefixEnd_4777831 2453323788951801447939661 := by
  unfold tailWord_4777831
  simp only [CollatzResearch.WordTrace]
  refine ⟨174261812753741750415741347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116174541835827833610494231 174261812753741750415741347)
  ·
    refine ⟨261392719130612625623612021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174261812753741750415741347 261392719130612625623612021)
    ·
      refine ⟨24505567418494933652213627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 261392719130612625623612021 24505567418494933652213627)
      ·
        refine ⟨36758351127742400478320441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24505567418494933652213627 36758351127742400478320441)
        ·
          refine ⟨27568763345806800358740331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36758351127742400478320441 27568763345806800358740331)
          ·
            refine ⟨41353145018710200538110497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27568763345806800358740331 41353145018710200538110497)
            ·
              refine ⟨31014858764032650403582873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41353145018710200538110497 31014858764032650403582873)
              ·
                refine ⟨23261144073024487802687155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31014858764032650403582873 23261144073024487802687155)
                ·
                  refine ⟨34891716109536731704030733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23261144073024487802687155 34891716109536731704030733)
                  ·
                    refine ⟨13084393541076274389011525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34891716109536731704030733 13084393541076274389011525)
                    ·
                      refine ⟨2453323788951801447939661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13084393541076274389011525 2453323788951801447939661)
                      ·
                        rfl

theorem cell23_4777831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_4777831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777831 prefixEnd_4777831 := by exact prefixLift 4777831
  have htrace : WordTrace (prefixWord ++ tailWord_4777831) baseStart_4777831 baseEnd_4777831 := by
    simpa [prefixWord, tailWord_4777831, baseEnd_4777831] using wordTrace_append hprefix tailTrace_4777831
  have hstable : (prefixWord ++ tailWord_4777831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777831).length < 2 ^ (prefixWord ++ tailWord_4777831).sum := by decide
  have hdescent : baseEnd_4777831 < baseStart_4777831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777932 : List Nat := [2, 2, 1, 4, 1, 4, 1, 1, 3, 1, 3]
def baseStart_4777932 : Nat := 118140960795 + 4777932 * 2 ^ 59
def prefixEnd_4777932 : Nat := 4983230072969 + 3 ^ 40 * 4777932 * 2
def baseEnd_4777932 : Nat := 2453375650497905552776697

theorem tailTrace_4777932 : CollatzResearch.WordTrace tailWord_4777932 prefixEnd_4777932 2453375650497905552776697 := by
  unfold tailWord_4777932
  simp only [CollatzResearch.WordTrace]
  refine ⟨87132748263187922332584025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116176997684250563110112033 87132748263187922332584025)
  ·
    refine ⟨65349561197390941749438019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87132748263187922332584025 65349561197390941749438019)
    ·
      refine ⟨98024341796086412624157029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65349561197390941749438019 98024341796086412624157029)
      ·
        refine ⟨18379564086766202367029443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98024341796086412624157029 18379564086766202367029443)
        ·
          refine ⟨27569346130149303550544165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18379564086766202367029443 27569346130149303550544165)
          ·
            refine ⟨5169252399402994415727031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27569346130149303550544165 5169252399402994415727031)
            ·
              refine ⟨7753878599104491623590547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5169252399402994415727031 7753878599104491623590547)
              ·
                refine ⟨11630817898656737435385821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7753878599104491623590547 11630817898656737435385821)
                ·
                  refine ⟨4361556711996276538269683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11630817898656737435385821 4361556711996276538269683)
                  ·
                    refine ⟨6542335067994414807404525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4361556711996276538269683 6542335067994414807404525)
                    ·
                      refine ⟨2453375650497905552776697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6542335067994414807404525 2453375650497905552776697)
                      ·
                        rfl

theorem cell23_4777932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_4777932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777932 prefixEnd_4777932 := by exact prefixLift 4777932
  have htrace : WordTrace (prefixWord ++ tailWord_4777932) baseStart_4777932 baseEnd_4777932 := by
    simpa [prefixWord, tailWord_4777932, baseEnd_4777932] using wordTrace_append hprefix tailTrace_4777932
  have hstable : (prefixWord ++ tailWord_4777932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777932).length < 2 ^ (prefixWord ++ tailWord_4777932).sum := by decide
  have hdescent : baseEnd_4777932 < baseStart_4777932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777955 : List Nat := [1, 1, 1, 6, 1, 2, 3, 2, 1, 1, 4]
def baseStart_4777955 : Nat := 118140960795 + 4777955 * 2 ^ 59
def prefixEnd_4777955 : Nat := 4983230072969 + 3 ^ 40 * 4777955 * 2
def baseEnd_4777955 : Nat := 2453387460552958962789091

theorem tailTrace_4777955 : CollatzResearch.WordTrace tailWord_4777955 prefixEnd_4777955 2453387460552958962789091 := by
  unfold tailWord_4777955
  simp only [CollatzResearch.WordTrace]
  refine ⟨174266335405292519593255319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116177556936861679728836879 174266335405292519593255319)
  ·
    refine ⟨261399503107938779389882979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174266335405292519593255319 261399503107938779389882979)
    ·
      refine ⟨392099254661908169084824469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261399503107938779389882979 392099254661908169084824469)
      ·
        refine ⟨18379652562276945425851147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 392099254661908169084824469 18379652562276945425851147)
        ·
          refine ⟨27569478843415418138776721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18379652562276945425851147 27569478843415418138776721)
          ·
            refine ⟨20677109132561563604082541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27569478843415418138776721 20677109132561563604082541)
            ·
              refine ⟨7753915924710586351530953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20677109132561563604082541 7753915924710586351530953)
              ·
                refine ⟨5815436943532939763648215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7753915924710586351530953 5815436943532939763648215)
                ·
                  refine ⟨8723155415299409645472323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5815436943532939763648215 8723155415299409645472323)
                  ·
                    refine ⟨13084733122949114468208485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8723155415299409645472323 13084733122949114468208485)
                    ·
                      refine ⟨2453387460552958962789091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13084733122949114468208485 2453387460552958962789091)
                      ·
                        rfl

theorem cell23_4777955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_4777955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777955 prefixEnd_4777955 := by exact prefixLift 4777955
  have htrace : WordTrace (prefixWord ++ tailWord_4777955) baseStart_4777955 baseEnd_4777955 := by
    simpa [prefixWord, tailWord_4777955, baseEnd_4777955] using wordTrace_append hprefix tailTrace_4777955
  have hstable : (prefixWord ++ tailWord_4777955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777955).length < 2 ^ (prefixWord ++ tailWord_4777955).sum := by decide
  have hdescent : baseEnd_4777955 < baseStart_4777955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777982 : List Nat := [4, 2, 2, 2, 1, 1, 1, 4, 2, 4]
def baseStart_4777982 : Nat := 118140960795 + 4777982 * 2 ^ 59
def prefixEnd_4777982 : Nat := 4983230072969 + 3 ^ 40 * 4777982 * 2
def baseEnd_4777982 : Nat := 817800441510210119050489

theorem tailTrace_4777982 : CollatzResearch.WordTrace tailWord_4777982 prefixEnd_4777982 817800441510210119050489 := by
  unfold tailWord_4777982
  simp only [CollatzResearch.WordTrace]
  refine ⟨21783415022024337900561025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116178213450796468802992133 21783415022024337900561025)
  ·
    refine ⟨16337561266518253425420769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21783415022024337900561025 16337561266518253425420769)
    ·
      refine ⟨12253170949888690069065577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16337561266518253425420769 12253170949888690069065577)
      ·
        refine ⟨9189878212416517551799183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12253170949888690069065577 9189878212416517551799183)
        ·
          refine ⟨13784817318624776327698775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9189878212416517551799183 13784817318624776327698775)
          ·
            refine ⟨20677225977937164491548163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13784817318624776327698775 20677225977937164491548163)
            ·
              refine ⟨31015838966905746737322245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20677225977937164491548163 31015838966905746737322245)
              ·
                refine ⟨5815469806294827513247921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31015838966905746737322245 5815469806294827513247921)
                ·
                  refine ⟨4361602354721120634935941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5815469806294827513247921 4361602354721120634935941)
                  ·
                    refine ⟨817800441510210119050489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4361602354721120634935941 817800441510210119050489)
                    ·
                      rfl

theorem cell23_4777982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_4777982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777982 prefixEnd_4777982 := by exact prefixLift 4777982
  have htrace : WordTrace (prefixWord ++ tailWord_4777982) baseStart_4777982 baseEnd_4777982 := by
    simpa [prefixWord, tailWord_4777982, baseEnd_4777982] using wordTrace_append hprefix tailTrace_4777982
  have hstable : (prefixWord ++ tailWord_4777982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777982).length < 2 ^ (prefixWord ++ tailWord_4777982).sum := by decide
  have hdescent : baseEnd_4777982 < baseStart_4777982 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4777989 : List Nat := [1, 3, 1, 1, 2, 5, 1, 4, 1, 2, 2]
def baseStart_4777989 : Nat := 118140960795 + 4777989 * 2 ^ 59
def prefixEnd_4777989 : Nat := 4983230072969 + 3 ^ 40 * 4777989 * 2
def baseEnd_4777989 : Nat := 2453404918895211829763935

theorem tailTrace_4777989 : CollatzResearch.WordTrace tailWord_4777989 prefixEnd_4777989 2453404918895211829763935 := by
  unfold tailWord_4777989
  simp only [CollatzResearch.WordTrace]
  refine ⟨174267575487169343399993021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116178383658112895599995347 174267575487169343399993021)
  ·
    refine ⟨65350340807688503774997383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174267575487169343399993021 65350340807688503774997383)
    ·
      refine ⟨98025511211532755662496075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65350340807688503774997383 98025511211532755662496075)
      ·
        refine ⟨147038266817299133493744113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98025511211532755662496075 147038266817299133493744113)
        ·
          refine ⟨110278700112974350120308085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147038266817299133493744113 110278700112974350120308085)
          ·
            refine ⟨10338628135591345323778883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 110278700112974350120308085 10338628135591345323778883)
            ·
              refine ⟨15507942203387017985668325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10338628135591345323778883 15507942203387017985668325)
              ·
                refine ⟨2907739163135065872312811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15507942203387017985668325 2907739163135065872312811)
                ·
                  refine ⟨4361608744702598808469217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2907739163135065872312811 4361608744702598808469217)
                  ·
                    refine ⟨3271206558526949106351913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4361608744702598808469217 3271206558526949106351913)
                    ·
                      refine ⟨2453404918895211829763935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3271206558526949106351913 2453404918895211829763935)
                      ·
                        rfl

theorem cell23_4777989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 4, 1, 2, 2].length) (baseStart_4777989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4777989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4777989 prefixEnd_4777989 := by exact prefixLift 4777989
  have htrace : WordTrace (prefixWord ++ tailWord_4777989) baseStart_4777989 baseEnd_4777989 := by
    simpa [prefixWord, tailWord_4777989, baseEnd_4777989] using wordTrace_append hprefix tailTrace_4777989
  have hstable : (prefixWord ++ tailWord_4777989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4777989).length < 2 ^ (prefixWord ++ tailWord_4777989).sum := by decide
  have hdescent : baseEnd_4777989 < baseStart_4777989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4777989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778001 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 5]
def baseStart_4778001 : Nat := 118140960795 + 4778001 * 2 ^ 59
def prefixEnd_4778001 : Nat := 4983230072969 + 3 ^ 40 * 4778001 * 2
def baseEnd_4778001 : Nat := 2453411080663065782813879

theorem tailTrace_4778001 : CollatzResearch.WordTrace tailWord_4778001 prefixEnd_4778001 2453411080663065782813879 := by
  unfold tailWord_4778001
  simp only [CollatzResearch.WordTrace]
  refine ⟨174268013163125869449429857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116178675442083912966286571 174268013163125869449429857)
  ·
    refine ⟨130701009872344402087072393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174268013163125869449429857 130701009872344402087072393)
    ·
      refine ⟨98025757404258301565304295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130701009872344402087072393 98025757404258301565304295)
      ·
        refine ⟨147038636106387452347956443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98025757404258301565304295 147038636106387452347956443)
        ·
          refine ⟨220557954159581178521934665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147038636106387452347956443 220557954159581178521934665)
          ·
            refine ⟨165418465619685883891450999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220557954159581178521934665 165418465619685883891450999)
            ·
              refine ⟨248127698429528825837176499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165418465619685883891450999 248127698429528825837176499)
              ·
                refine ⟨372191547644293238755764749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 248127698429528825837176499 372191547644293238755764749)
                ·
                  refine ⟨139571830366609964533411781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 372191547644293238755764749 139571830366609964533411781)
                  ·
                    refine ⟨26169718193739368350014709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 139571830366609964533411781 26169718193739368350014709)
                    ·
                      refine ⟨2453411080663065782813879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26169718193739368350014709 2453411080663065782813879)
                      ·
                        rfl

theorem cell23_4778001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_4778001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778001 prefixEnd_4778001 := by exact prefixLift 4778001
  have htrace : WordTrace (prefixWord ++ tailWord_4778001) baseStart_4778001 baseEnd_4778001 := by
    simpa [prefixWord, tailWord_4778001, baseEnd_4778001] using wordTrace_append hprefix tailTrace_4778001
  have hstable : (prefixWord ++ tailWord_4778001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778001).length < 2 ^ (prefixWord ++ tailWord_4778001).sum := by decide
  have hdescent : baseEnd_4778001 < baseStart_4778001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778015 : List Nat := [1, 1, 2, 4, 1, 2, 1, 3, 3, 3, 2]
def baseStart_4778015 : Nat := 118140960795 + 4778015 * 2 ^ 59
def prefixEnd_4778015 : Nat := 4983230072969 + 3 ^ 40 * 4778015 * 2
def baseEnd_4778015 : Nat := 2453418269392228728038815

theorem tailTrace_4778015 : CollatzResearch.WordTrace tailWord_4778015 prefixEnd_4778015 2453418269392228728038815 := by
  unfold tailWord_4778015
  simp only [CollatzResearch.WordTrace]
  refine ⟨174268523785075149840439499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116179015856716766560292999 174268523785075149840439499)
  ·
    refine ⟨261402785677612724760659249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174268523785075149840439499 261402785677612724760659249)
    ·
      refine ⟨196052089258209543570494437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261402785677612724760659249 196052089258209543570494437)
      ·
        refine ⟨36759766735914289419467707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 196052089258209543570494437 36759766735914289419467707)
        ·
          refine ⟨55139650103871434129201561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36759766735914289419467707 55139650103871434129201561)
          ·
            refine ⟨41354737577903575596901171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55139650103871434129201561 41354737577903575596901171)
            ·
              refine ⟨62032106366855363395351757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41354737577903575596901171 62032106366855363395351757)
              ·
                refine ⟨23262039887570761273256909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62032106366855363395351757 23262039887570761273256909)
                ·
                  refine ⟨8723264957839035477471341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23262039887570761273256909 8723264957839035477471341)
                  ·
                    refine ⟨3271224359189638304051753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8723264957839035477471341 3271224359189638304051753)
                    ·
                      refine ⟨2453418269392228728038815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3271224359189638304051753 2453418269392228728038815)
                      ·
                        rfl

theorem cell23_4778015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 3, 3, 2].length) (baseStart_4778015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778015 prefixEnd_4778015 := by exact prefixLift 4778015
  have htrace : WordTrace (prefixWord ++ tailWord_4778015) baseStart_4778015 baseEnd_4778015 := by
    simpa [prefixWord, tailWord_4778015, baseEnd_4778015] using wordTrace_append hprefix tailTrace_4778015
  have hstable : (prefixWord ++ tailWord_4778015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778015).length < 2 ^ (prefixWord ++ tailWord_4778015).sum := by decide
  have hdescent : baseEnd_4778015 < baseStart_4778015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778018 : List Nat := [3, 3, 1, 1, 1, 2, 2, 1, 2, 2, 5]
def baseStart_4778018 : Nat := 118140960795 + 4778018 * 2 ^ 59
def prefixEnd_4778018 : Nat := 4983230072969 + 3 ^ 40 * 4778018 * 2
def baseEnd_4778018 : Nat := 2453419809834192216301301

theorem tailTrace_4778018 : CollatzResearch.WordTrace tailWord_4778018 prefixEnd_4778018 2453419809834192216301301 := by
  unfold tailWord_4778018
  simp only [CollatzResearch.WordTrace]
  refine ⟨43567158301016070338199677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116179088802709520901865805 43567158301016070338199677)
  ·
    refine ⟨16337684362881026376824879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43567158301016070338199677 16337684362881026376824879)
    ·
      refine ⟨24506526544321539565237319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16337684362881026376824879 24506526544321539565237319)
      ·
        refine ⟨36759789816482309347855979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24506526544321539565237319 36759789816482309347855979)
        ·
          refine ⟨55139684724723464021783969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36759789816482309347855979 55139684724723464021783969)
          ·
            refine ⟨41354763543542598016337977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55139684724723464021783969 41354763543542598016337977)
            ·
              refine ⟨31016072657656948512253483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41354763543542598016337977 31016072657656948512253483)
              ·
                refine ⟨46524108986485422768380225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31016072657656948512253483 46524108986485422768380225)
                ·
                  refine ⟨34893081739864067076285169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46524108986485422768380225 34893081739864067076285169)
                  ·
                    refine ⟨26169811304898050307213877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34893081739864067076285169 26169811304898050307213877)
                    ·
                      refine ⟨2453419809834192216301301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26169811304898050307213877 2453419809834192216301301)
                      ·
                        rfl

theorem cell23_4778018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_4778018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778018 prefixEnd_4778018 := by exact prefixLift 4778018
  have htrace : WordTrace (prefixWord ++ tailWord_4778018) baseStart_4778018 baseEnd_4778018 := by
    simpa [prefixWord, tailWord_4778018, baseEnd_4778018] using wordTrace_append hprefix tailTrace_4778018
  have hstable : (prefixWord ++ tailWord_4778018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778018).length < 2 ^ (prefixWord ++ tailWord_4778018).sum := by decide
  have hdescent : baseEnd_4778018 < baseStart_4778018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778023 : List Nat := [1, 1, 7, 1, 2, 1, 2, 3, 1, 2, 2]
def baseStart_4778023 : Nat := 118140960795 + 4778023 * 2 ^ 59
def prefixEnd_4778023 : Nat := 4983230072969 + 3 ^ 40 * 4778023 * 2
def baseEnd_4778023 : Nat := 2453422377237464696738779

theorem tailTrace_4778023 : CollatzResearch.WordTrace tailWord_4778023 prefixEnd_4778023 2453422377237464696738779 := by
  unfold tailWord_4778023
  simp only [CollatzResearch.WordTrace]
  refine ⟨174268815569046167206730723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116179210379364111471153815 174268815569046167206730723)
  ·
    refine ⟨261403223353569250810096085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174268815569046167206730723 261403223353569250810096085)
    ·
      refine ⟨6126638047349279315861627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 261403223353569250810096085 6126638047349279315861627)
      ·
        refine ⟨9189957071023918973792441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6126638047349279315861627 9189957071023918973792441)
        ·
          refine ⟨6892467803267939230344331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9189957071023918973792441 6892467803267939230344331)
          ·
            refine ⟨10338701704901908845516497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6892467803267939230344331 10338701704901908845516497)
            ·
              refine ⟨7754026278676431634137373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10338701704901908845516497 7754026278676431634137373)
              ·
                refine ⟨2907759854503661862801515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7754026278676431634137373 2907759854503661862801515)
                ·
                  refine ⟨4361639781755492794202273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2907759854503661862801515 4361639781755492794202273)
                  ·
                    refine ⟨3271229836316619595651705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4361639781755492794202273 3271229836316619595651705)
                    ·
                      refine ⟨2453422377237464696738779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3271229836316619595651705 2453422377237464696738779)
                      ·
                        rfl

theorem cell23_4778023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_4778023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778023 prefixEnd_4778023 := by exact prefixLift 4778023
  have htrace : WordTrace (prefixWord ++ tailWord_4778023) baseStart_4778023 baseEnd_4778023 := by
    simpa [prefixWord, tailWord_4778023, baseEnd_4778023] using wordTrace_append hprefix tailTrace_4778023
  have hstable : (prefixWord ++ tailWord_4778023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778023).length < 2 ^ (prefixWord ++ tailWord_4778023).sum := by decide
  have hdescent : baseEnd_4778023 < baseStart_4778023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778032 : List Nat := [2, 1, 1, 1, 2, 6, 1, 3, 1, 3, 2]
def baseStart_4778032 : Nat := 118140960795 + 4778032 * 2 ^ 59
def prefixEnd_4778032 : Nat := 4983230072969 + 3 ^ 40 * 4778032 * 2
def baseEnd_4778032 : Nat := 2453426998563355161526237

theorem tailTrace_4778032 : CollatzResearch.WordTrace tailWord_4778032 prefixEnd_4778032 2453426998563355161526237 := by
  unfold tailWord_4778032
  simp only [CollatzResearch.WordTrace]
  refine ⟨87134571913006780871904175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116179429217342374495872233 87134571913006780871904175)
  ·
    refine ⟨130701857869510171307856263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87134571913006780871904175 130701857869510171307856263)
    ·
      refine ⟨196052786804265256961784395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130701857869510171307856263 196052786804265256961784395)
      ·
        refine ⟨294079180206397885442676593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196052786804265256961784395 294079180206397885442676593)
        ·
          refine ⟨220559385154798414082007445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 294079180206397885442676593 220559385154798414082007445)
          ·
            refine ⟨10338721179131175660094099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 220559385154798414082007445 10338721179131175660094099)
            ·
              refine ⟨15508081768696763490141149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10338721179131175660094099 15508081768696763490141149)
              ·
                refine ⟨5815530663261286308802931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15508081768696763490141149 5815530663261286308802931)
                ·
                  refine ⟨8723295994891929463204397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5815530663261286308802931 8723295994891929463204397)
                  ·
                    refine ⟨3271235998084473548701649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8723295994891929463204397 3271235998084473548701649)
                    ·
                      refine ⟨2453426998563355161526237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3271235998084473548701649 2453426998563355161526237)
                      ·
                        rfl

theorem cell23_4778032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 3, 1, 3, 2].length) (baseStart_4778032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778032 prefixEnd_4778032 := by exact prefixLift 4778032
  have htrace : WordTrace (prefixWord ++ tailWord_4778032) baseStart_4778032 baseEnd_4778032 := by
    simpa [prefixWord, tailWord_4778032, baseEnd_4778032] using wordTrace_append hprefix tailTrace_4778032
  have hstable : (prefixWord ++ tailWord_4778032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778032).length < 2 ^ (prefixWord ++ tailWord_4778032).sum := by decide
  have hdescent : baseEnd_4778032 < baseStart_4778032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778062 : List Nat := [4, 1, 1, 1, 1, 4, 3, 1, 1, 4, 2]
def baseStart_4778062 : Nat := 118140960795 + 4778062 * 2 ^ 59
def prefixEnd_4778062 : Nat := 4983230072969 + 3 ^ 40 * 4778062 * 2
def baseEnd_4778062 : Nat := 2453442402982990044151099

theorem tailTrace_4778062 : CollatzResearch.WordTrace tailWord_4778062 prefixEnd_4778062 2453442402982990044151099 := by
  unfold tailWord_4778062
  simp only [CollatzResearch.WordTrace]
  refine ⟨21783779751988109608425055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116180158677269917911600293 21783779751988109608425055)
  ·
    refine ⟨32675669627982164412637583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21783779751988109608425055 32675669627982164412637583)
    ·
      refine ⟨49013504441973246618956375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32675669627982164412637583 49013504441973246618956375)
      ·
        refine ⟨73520256662959869928434563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49013504441973246618956375 73520256662959869928434563)
        ·
          refine ⟨110280384994439804892651845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73520256662959869928434563 110280384994439804892651845)
          ·
            refine ⟨20677572186457463417372221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110280384994439804892651845 20677572186457463417372221)
            ·
              refine ⟨7754089569921548781514583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20677572186457463417372221 7754089569921548781514583)
              ·
                refine ⟨11631134354882323172271875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7754089569921548781514583 11631134354882323172271875)
                ·
                  refine ⟨17446701532323484758407813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11631134354882323172271875 17446701532323484758407813)
                  ·
                    refine ⟨3271256537310653392201465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17446701532323484758407813 3271256537310653392201465)
                    ·
                      refine ⟨2453442402982990044151099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3271256537310653392201465 2453442402982990044151099)
                      ·
                        rfl

theorem cell23_4778062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 1, 4, 2].length) (baseStart_4778062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778062 prefixEnd_4778062 := by exact prefixLift 4778062
  have htrace : WordTrace (prefixWord ++ tailWord_4778062) baseStart_4778062 baseEnd_4778062 := by
    simpa [prefixWord, tailWord_4778062, baseEnd_4778062] using wordTrace_append hprefix tailTrace_4778062
  have hstable : (prefixWord ++ tailWord_4778062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778062).length < 2 ^ (prefixWord ++ tailWord_4778062).sum := by decide
  have hdescent : baseEnd_4778062 < baseStart_4778062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778082 : List Nat := [3, 3, 2, 2, 2, 1, 1, 1, 2, 1, 5]
def baseStart_4778082 : Nat := 118140960795 + 4778082 * 2 ^ 59
def prefixEnd_4778082 : Nat := 4983230072969 + 3 ^ 40 * 4778082 * 2
def baseEnd_4778082 : Nat := 2453452672596079965901007

theorem tailTrace_4778082 : CollatzResearch.WordTrace tailWord_4778082 prefixEnd_4778082 2453452672596079965901007 := by
  unfold tailWord_4778082
  simp only [CollatzResearch.WordTrace]
  refine ⟨43567741868958105070782125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116180644983888280188752333 43567741868958105070782125)
  ·
    refine ⟨16337903200859289401543297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43567741868958105070782125 16337903200859289401543297)
    ·
      refine ⟨12253427400644467051157473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16337903200859289401543297 12253427400644467051157473)
      ·
        refine ⟨9190070550483350288368105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12253427400644467051157473 9190070550483350288368105)
        ·
          refine ⟨6892552912862512716276079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9190070550483350288368105 6892552912862512716276079)
          ·
            refine ⟨10338829369293769074414119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6892552912862512716276079 10338829369293769074414119)
            ·
              refine ⟨15508244053940653611621179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10338829369293769074414119 15508244053940653611621179)
              ·
                refine ⟨23262366080910980417431769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15508244053940653611621179 23262366080910980417431769)
                ·
                  refine ⟨17446774560683235313073827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23262366080910980417431769 17446774560683235313073827)
                  ·
                    refine ⟨26170161841024852969610741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17446774560683235313073827 26170161841024852969610741)
                    ·
                      refine ⟨2453452672596079965901007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26170161841024852969610741 2453452672596079965901007)
                      ·
                        rfl

theorem cell23_4778082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_4778082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778082 prefixEnd_4778082 := by exact prefixLift 4778082
  have htrace : WordTrace (prefixWord ++ tailWord_4778082) baseStart_4778082 baseEnd_4778082 := by
    simpa [prefixWord, tailWord_4778082, baseEnd_4778082] using wordTrace_append hprefix tailTrace_4778082
  have hstable : (prefixWord ++ tailWord_4778082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778082).length < 2 ^ (prefixWord ++ tailWord_4778082).sum := by decide
  have hdescent : baseEnd_4778082 < baseStart_4778082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778102 : List Nat := [5, 1, 1, 2, 1, 4, 1, 1, 7]
def baseStart_4778102 : Nat := 118140960795 + 4778102 * 2 ^ 59
def prefixEnd_4778102 : Nat := 4983230072969 + 3 ^ 40 * 4778102 * 2
def baseEnd_4778102 : Nat := 272606993578796654183435

theorem tailTrace_4778102 : CollatzResearch.WordTrace tailWord_4778102 prefixEnd_4778102 272606993578796654183435 := by
  unfold tailWord_4778102
  simp only [CollatzResearch.WordTrace]
  refine ⟨10891981058484997731178535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116181131290506642465904373 10891981058484997731178535)
  ·
    refine ⟨16337971587727496596767803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10891981058484997731178535 16337971587727496596767803)
    ·
      refine ⟨24506957381591244895151705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16337971587727496596767803 24506957381591244895151705)
      ·
        refine ⟨18380218036193433671363779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24506957381591244895151705 18380218036193433671363779)
        ·
          refine ⟨27570327054290150507045669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18380218036193433671363779 27570327054290150507045669)
          ·
            refine ⟨5169436322679403220071063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27570327054290150507045669 5169436322679403220071063)
            ·
              refine ⟨7754154484019104830106595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5169436322679403220071063 7754154484019104830106595)
              ·
                refine ⟨11631231726028657245159893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7754154484019104830106595 11631231726028657245159893)
                ·
                  refine ⟨272606993578796654183435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11631231726028657245159893 272606993578796654183435)
                  ·
                    rfl

theorem cell23_4778102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_4778102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778102 prefixEnd_4778102 := by exact prefixLift 4778102
  have htrace : WordTrace (prefixWord ++ tailWord_4778102) baseStart_4778102 baseEnd_4778102 := by
    simpa [prefixWord, tailWord_4778102, baseEnd_4778102] using wordTrace_append hprefix tailTrace_4778102
  have hstable : (prefixWord ++ tailWord_4778102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778102).length < 2 ^ (prefixWord ++ tailWord_4778102).sum := by decide
  have hdescent : baseEnd_4778102 < baseStart_4778102 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778108 : List Nat := [2, 2, 2, 1, 1, 4, 1, 1, 1, 1, 7]
def baseStart_4778108 : Nat := 118140960795 + 4778108 * 2 ^ 59
def prefixEnd_4778108 : Nat := 4983230072969 + 3 ^ 40 * 4778108 * 2
def baseEnd_4778108 : Nat := 2453466023093096864175887

theorem tailTrace_4778108 : CollatzResearch.WordTrace tailWord_4778108 prefixEnd_4778108 2453466023093096864175887 := by
  unfold tailWord_4778108
  simp only [CollatzResearch.WordTrace]
  refine ⟨87135957886869113361787489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116181277182492151149049985 87135957886869113361787489)
  ·
    refine ⟨65351968415151835021340617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87135957886869113361787489 65351968415151835021340617)
    ·
      refine ⟨49013976311363876266005463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65351968415151835021340617 49013976311363876266005463)
      ·
        refine ⟨73520964467045814399008195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49013976311363876266005463 73520964467045814399008195)
        ·
          refine ⟨110281446700568721598512293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73520964467045814399008195 110281446700568721598512293)
          ·
            refine ⟨20677771256356635299721055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110281446700568721598512293 20677771256356635299721055)
            ·
              refine ⟨31016656884534952949581583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20677771256356635299721055 31016656884534952949581583)
              ·
                refine ⟨46524985326802429424372375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31016656884534952949581583 46524985326802429424372375)
                ·
                  refine ⟨69787477990203644136558563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46524985326802429424372375 69787477990203644136558563)
                  ·
                    refine ⟨104681216985305466204837845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69787477990203644136558563 104681216985305466204837845)
                    ·
                      refine ⟨2453466023093096864175887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 104681216985305466204837845 2453466023093096864175887)
                      ·
                        rfl

theorem cell23_4778108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_4778108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778108 prefixEnd_4778108 := by exact prefixLift 4778108
  have htrace : WordTrace (prefixWord ++ tailWord_4778108) baseStart_4778108 baseEnd_4778108 := by
    simpa [prefixWord, tailWord_4778108, baseEnd_4778108] using wordTrace_append hprefix tailTrace_4778108
  have hstable : (prefixWord ++ tailWord_4778108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778108).length < 2 ^ (prefixWord ++ tailWord_4778108).sum := by decide
  have hdescent : baseEnd_4778108 < baseStart_4778108 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778113 : List Nat := [1, 2, 4, 2, 3, 2, 2, 1, 2, 2, 2]
def baseStart_4778113 : Nat := 118140960795 + 4778113 * 2 ^ 59
def prefixEnd_4778113 : Nat := 4983230072969 + 3 ^ 40 * 4778113 * 2
def baseEnd_4778113 : Nat := 2453468590496369344613365

theorem tailTrace_4778113 : CollatzResearch.WordTrace tailWord_4778113 prefixEnd_4778113 2453468590496369344613365 := by
  unfold tailWord_4778113
  simp only [CollatzResearch.WordTrace]
  refine ⟨174272098138720112577506993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116181398759146741718337995 174272098138720112577506993)
  ·
    refine ⟨130704073604040084433130245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174272098138720112577506993 130704073604040084433130245)
    ·
      refine ⟨24507013800757515831211921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130704073604040084433130245 24507013800757515831211921)
      ·
        refine ⟨18380260350568136873408941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24507013800757515831211921 18380260350568136873408941)
        ·
          refine ⟨6892597631463051327528353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18380260350568136873408941 6892597631463051327528353)
          ·
            refine ⟨5169448223597288495646265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6892597631463051327528353 5169448223597288495646265)
            ·
              refine ⟨3877086167697966371734699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5169448223597288495646265 3877086167697966371734699)
              ·
                refine ⟨5815629251546949557602049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3877086167697966371734699 5815629251546949557602049)
                ·
                  refine ⟨4361721938660212168201537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5815629251546949557602049 4361721938660212168201537)
                  ·
                    refine ⟨3271291453995159126151153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4361721938660212168201537 3271291453995159126151153)
                    ·
                      refine ⟨2453468590496369344613365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3271291453995159126151153 2453468590496369344613365)
                      ·
                        rfl

theorem cell23_4778113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_4778113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778113 prefixEnd_4778113 := by exact prefixLift 4778113
  have htrace : WordTrace (prefixWord ++ tailWord_4778113) baseStart_4778113 baseEnd_4778113 := by
    simpa [prefixWord, tailWord_4778113, baseEnd_4778113] using wordTrace_append hprefix tailTrace_4778113
  have hstable : (prefixWord ++ tailWord_4778113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778113).length < 2 ^ (prefixWord ++ tailWord_4778113).sum := by decide
  have hdescent : baseEnd_4778113 < baseStart_4778113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778212 : List Nat := [2, 3, 1, 1, 1, 2, 1, 3, 4, 3, 2]
def baseStart_4778212 : Nat := 118140960795 + 4778212 * 2 ^ 59
def prefixEnd_4778212 : Nat := 4983230072969 + 3 ^ 40 * 4778212 * 2
def baseEnd_4778212 : Nat := 2453519425081164457275409

theorem tailTrace_4778212 : CollatzResearch.WordTrace tailWord_4778212 prefixEnd_4778212 2453519425081164457275409 := by
  unfold tailWord_4778212
  simp only [CollatzResearch.WordTrace]
  refine ⟨87137854482680726242680445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116183805976907634990240593 87137854482680726242680445)
  ·
    refine ⟨32676695431005272341005167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87137854482680726242680445 32676695431005272341005167)
    ·
      refine ⟨49015043146507908511507751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32676695431005272341005167 49015043146507908511507751)
      ·
        refine ⟨73522564719761862767261627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49015043146507908511507751 73522564719761862767261627)
        ·
          refine ⟨110283847079642794150892441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73522564719761862767261627 110283847079642794150892441)
          ·
            refine ⟨82712885309732095613169331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110283847079642794150892441 82712885309732095613169331)
            ·
              refine ⟨124069327964598143419753997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82712885309732095613169331 124069327964598143419753997)
              ·
                refine ⟨46525997986724303782407749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124069327964598143419753997 46525997986724303782407749)
                ·
                  refine ⟨8723624622510806959201453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46525997986724303782407749 8723624622510806959201453)
                  ·
                    refine ⟨3271359233441552609700545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8723624622510806959201453 3271359233441552609700545)
                    ·
                      refine ⟨2453519425081164457275409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3271359233441552609700545 2453519425081164457275409)
                      ·
                        rfl

theorem cell23_4778212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 4, 3, 2].length) (baseStart_4778212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778212 prefixEnd_4778212 := by exact prefixLift 4778212
  have htrace : WordTrace (prefixWord ++ tailWord_4778212) baseStart_4778212 baseEnd_4778212 := by
    simpa [prefixWord, tailWord_4778212, baseEnd_4778212] using wordTrace_append hprefix tailTrace_4778212
  have hstable : (prefixWord ++ tailWord_4778212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778212).length < 2 ^ (prefixWord ++ tailWord_4778212).sum := by decide
  have hdescent : baseEnd_4778212 < baseStart_4778212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778219 : List Nat := [1, 1, 1, 1, 2, 5, 1, 6, 1, 1, 3]
def baseStart_4778219 : Nat := 118140960795 + 4778219 * 2 ^ 59
def prefixEnd_4778219 : Nat := 4983230072969 + 3 ^ 40 * 4778219 * 2
def baseEnd_4778219 : Nat := 2453523019445745929887877

theorem tailTrace_4778219 : CollatzResearch.WordTrace tailWord_4778219 prefixEnd_4778219 2453523019445745929887877 := by
  unfold tailWord_4778219
  simp only [CollatzResearch.WordTrace]
  refine ⟨174275964276336092680865711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116183976184224061787243807 174275964276336092680865711)
  ·
    refine ⟨261413946414504139021298567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174275964276336092680865711 261413946414504139021298567)
    ·
      refine ⟨392120919621756208531947851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261413946414504139021298567 392120919621756208531947851)
      ·
        refine ⟨588181379432634312797921777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 392120919621756208531947851 588181379432634312797921777)
        ·
          refine ⟨441136034574475734598441333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 588181379432634312797921777 441136034574475734598441333)
          ·
            refine ⟨41356503241357100118603875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 441136034574475734598441333 41356503241357100118603875)
            ·
              refine ⟨62034754862035650177905813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41356503241357100118603875 62034754862035650177905813)
              ·
                refine ⟨2907879134157921102089335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 62034754862035650177905813 2907879134157921102089335)
                ·
                  refine ⟨4361818701236881653134003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2907879134157921102089335 4361818701236881653134003)
                  ·
                    refine ⟨6542728051855322479701005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4361818701236881653134003 6542728051855322479701005)
                    ·
                      refine ⟨2453523019445745929887877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6542728051855322479701005 2453523019445745929887877)
                      ·
                        rfl

theorem cell23_4778219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 6, 1, 1, 3].length) (baseStart_4778219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778219 prefixEnd_4778219 := by exact prefixLift 4778219
  have htrace : WordTrace (prefixWord ++ tailWord_4778219) baseStart_4778219 baseEnd_4778219 := by
    simpa [prefixWord, tailWord_4778219, baseEnd_4778219] using wordTrace_append hprefix tailTrace_4778219
  have hstable : (prefixWord ++ tailWord_4778219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778219).length < 2 ^ (prefixWord ++ tailWord_4778219).sum := by decide
  have hdescent : baseEnd_4778219 < baseStart_4778219 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778225 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 5, 1, 4]
def baseStart_4778225 : Nat := 118140960795 + 4778225 * 2 ^ 59
def prefixEnd_4778225 : Nat := 4983230072969 + 3 ^ 40 * 4778225 * 2
def baseEnd_4778225 : Nat := 2453526100329672906412849

theorem tailTrace_4778225 : CollatzResearch.WordTrace tailWord_4778225 prefixEnd_4778225 2453526100329672906412849 := by
  unfold tailWord_4778225
  simp only [CollatzResearch.WordTrace]
  refine ⟨174276183114314355705584129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116184122076209570470389419 174276183114314355705584129)
  ·
    refine ⟨130707137335735766779188097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174276183114314355705584129 130707137335735766779188097)
    ·
      refine ⟨98030353001801825084391073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130707137335735766779188097 98030353001801825084391073)
      ·
        refine ⟨73522764751351368813293305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98030353001801825084391073 73522764751351368813293305)
        ·
          refine ⟨55142073563513526609969979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73522764751351368813293305 55142073563513526609969979)
          ·
            refine ⟨82713110345270289914954969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55142073563513526609969979 82713110345270289914954969)
            ·
              refine ⟨62034832758952717436216227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82713110345270289914954969 62034832758952717436216227)
              ·
                refine ⟨93052249138429076154324341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62034832758952717436216227 93052249138429076154324341)
                ·
                  refine ⟨8723648356727725889467907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 93052249138429076154324341 8723648356727725889467907)
                  ·
                    refine ⟨13085472535091588834201861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8723648356727725889467907 13085472535091588834201861)
                    ·
                      refine ⟨2453526100329672906412849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13085472535091588834201861 2453526100329672906412849)
                      ·
                        rfl

theorem cell23_4778225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_4778225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778225 prefixEnd_4778225 := by exact prefixLift 4778225
  have htrace : WordTrace (prefixWord ++ tailWord_4778225) baseStart_4778225 baseEnd_4778225 := by
    simpa [prefixWord, tailWord_4778225, baseEnd_4778225] using wordTrace_append hprefix tailTrace_4778225
  have hstable : (prefixWord ++ tailWord_4778225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778225).length < 2 ^ (prefixWord ++ tailWord_4778225).sum := by decide
  have hdescent : baseEnd_4778225 < baseStart_4778225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778255 : List Nat := [1, 1, 2, 1, 1, 1, 3, 6, 1, 2, 4]
def baseStart_4778255 : Nat := 118140960795 + 4778255 * 2 ^ 59
def prefixEnd_4778255 : Nat := 4983230072969 + 3 ^ 40 * 4778255 * 2
def baseEnd_4778255 : Nat := 2453541504749307789037711

theorem tailTrace_4778255 : CollatzResearch.WordTrace tailWord_4778255 prefixEnd_4778255 2453541504749307789037711 := by
  unfold tailWord_4778255
  simp only [CollatzResearch.WordTrace]
  refine ⟨174277277304205670829176219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116184851536137113886117479 174277277304205670829176219)
  ·
    refine ⟨261415915956308506243764329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174277277304205670829176219 261415915956308506243764329)
    ·
      refine ⟨196061936967231379682823247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261415915956308506243764329 196061936967231379682823247)
      ·
        refine ⟨294092905450847069524234871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196061936967231379682823247 294092905450847069524234871)
        ·
          refine ⟨441139358176270604286352307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294092905450847069524234871 441139358176270604286352307)
          ·
            refine ⟨661709037264405906429528461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 441139358176270604286352307 661709037264405906429528461)
            ·
              refine ⟨248140888974152214911073173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 661709037264405906429528461 248140888974152214911073173)
              ·
                refine ⟨11631604170663385073956555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 248140888974152214911073173 11631604170663385073956555)
                ·
                  refine ⟨17447406255995077610934833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11631604170663385073956555 17447406255995077610934833)
                  ·
                    refine ⟨13085554691996308208201125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17447406255995077610934833 13085554691996308208201125)
                    ·
                      refine ⟨2453541504749307789037711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13085554691996308208201125 2453541504749307789037711)
                      ·
                        rfl

theorem cell23_4778255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 2, 4].length) (baseStart_4778255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778255 prefixEnd_4778255 := by exact prefixLift 4778255
  have htrace : WordTrace (prefixWord ++ tailWord_4778255) baseStart_4778255 baseEnd_4778255 := by
    simpa [prefixWord, tailWord_4778255, baseEnd_4778255] using wordTrace_append hprefix tailTrace_4778255
  have hstable : (prefixWord ++ tailWord_4778255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778255).length < 2 ^ (prefixWord ++ tailWord_4778255).sum := by decide
  have hdescent : baseEnd_4778255 < baseStart_4778255 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778276 : List Nat := [2, 3, 1, 3, 1, 2, 3, 1, 3, 2, 2]
def baseStart_4778276 : Nat := 118140960795 + 4778276 * 2 ^ 59
def prefixEnd_4778276 : Nat := 4983230072969 + 3 ^ 40 * 4778276 * 2
def baseEnd_4778276 : Nat := 2453552287843052206875115

theorem tailTrace_4778276 : CollatzResearch.WordTrace tailWord_4778276 prefixEnd_4778276 2453552287843052206875115 := by
  unfold tailWord_4778276
  simp only [CollatzResearch.WordTrace]
  refine ⟨87139021618564795707845341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116185362158086394277127121 87139021618564795707845341)
  ·
    refine ⟨32677133106961798390442003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87139021618564795707845341 32677133106961798390442003)
    ·
      refine ⟨49015699660442697585663005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32677133106961798390442003 49015699660442697585663005)
      ·
        refine ⟨18380887372666011594623627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49015699660442697585663005 18380887372666011594623627)
        ·
          refine ⟨27571331058999017391935441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18380887372666011594623627 27571331058999017391935441)
          ·
            refine ⟨20678498294249263043951581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27571331058999017391935441 20678498294249263043951581)
            ·
              refine ⟨7754436860343473641481843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20678498294249263043951581 7754436860343473641481843)
              ·
                refine ⟨11631655290515210462222765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7754436860343473641481843 11631655290515210462222765)
                ·
                  refine ⟨4361870733943203923333537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11631655290515210462222765 4361870733943203923333537)
                  ·
                    refine ⟨3271403050457402942500153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4361870733943203923333537 3271403050457402942500153)
                    ·
                      refine ⟨2453552287843052206875115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3271403050457402942500153 2453552287843052206875115)
                      ·
                        rfl

theorem cell23_4778276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_4778276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778276 prefixEnd_4778276 := by exact prefixLift 4778276
  have htrace : WordTrace (prefixWord ++ tailWord_4778276) baseStart_4778276 baseEnd_4778276 := by
    simpa [prefixWord, tailWord_4778276, baseEnd_4778276] using wordTrace_append hprefix tailTrace_4778276
  have hstable : (prefixWord ++ tailWord_4778276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778276).length < 2 ^ (prefixWord ++ tailWord_4778276).sum := by decide
  have hdescent : baseEnd_4778276 < baseStart_4778276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778335 : List Nat := [1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 5]
def baseStart_4778335 : Nat := 118140960795 + 4778335 * 2 ^ 59
def prefixEnd_4778335 : Nat := 4983230072969 + 3 ^ 40 * 4778335 * 2
def baseEnd_4778335 : Nat := 2453582583201667476037343

theorem tailTrace_4778335 : CollatzResearch.WordTrace tailWord_4778335 prefixEnd_4778335 2453582583201667476037343 := by
  unfold tailWord_4778335
  simp only [CollatzResearch.WordTrace]
  refine ⟨174280195143915844492088459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116186796762610562994725639 174280195143915844492088459)
  ·
    refine ⟨261420292715873766738132689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174280195143915844492088459 261420292715873766738132689)
    ·
      refine ⟨196065219536905325053599517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261420292715873766738132689 196065219536905325053599517)
      ·
        refine ⟨73524457326339496895099819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196065219536905325053599517 73524457326339496895099819)
        ·
          refine ⟨110286685989509245342649729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73524457326339496895099819 110286685989509245342649729)
          ·
            refine ⟨82715014492131934006987297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110286685989509245342649729 82715014492131934006987297)
            ·
              refine ⟨62036260869098950505240473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82715014492131934006987297 62036260869098950505240473)
              ·
                refine ⟨46527195651824212878930355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62036260869098950505240473 46527195651824212878930355)
                ·
                  refine ⟨69790793477736319318395533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46527195651824212878930355 69790793477736319318395533)
                  ·
                    refine ⟨26171547554151119744398325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 69790793477736319318395533 26171547554151119744398325)
                    ·
                      refine ⟨2453582583201667476037343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26171547554151119744398325 2453582583201667476037343)
                      ·
                        rfl

theorem cell23_4778335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_4778335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778335 prefixEnd_4778335 := by exact prefixLift 4778335
  have htrace : WordTrace (prefixWord ++ tailWord_4778335) baseStart_4778335 baseEnd_4778335 := by
    simpa [prefixWord, tailWord_4778335, baseEnd_4778335] using wordTrace_append hprefix tailTrace_4778335
  have hstable : (prefixWord ++ tailWord_4778335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778335).length < 2 ^ (prefixWord ++ tailWord_4778335).sum := by decide
  have hdescent : baseEnd_4778335 < baseStart_4778335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778355 : List Nat := [1, 1, 1, 2, 2, 1, 2, 6, 7]
def baseStart_4778355 : Nat := 118140960795 + 4778355 * 2 ^ 59
def prefixEnd_4778355 : Nat := 4983230072969 + 3 ^ 40 * 4778355 * 2
def baseEnd_4778355 : Nat := 272621428090528599754139

theorem tailTrace_4778355 : CollatzResearch.WordTrace tailWord_4778355 prefixEnd_4778355 272621428090528599754139 := by
  unfold tailWord_4778355
  simp only [CollatzResearch.WordTrace]
  refine ⟨174280924603843387907816519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116187283069228925271877679 174280924603843387907816519)
  ·
    refine ⟨261421386905765081861724779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174280924603843387907816519 261421386905765081861724779)
    ·
      refine ⟨392132080358647622792587169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261421386905765081861724779 392132080358647622792587169)
      ·
        refine ⟨294099060268985717094440377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 392132080358647622792587169 294099060268985717094440377)
        ·
          refine ⟨220574295201739287820830283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 294099060268985717094440377 220574295201739287820830283)
          ·
            refine ⟨330861442802608931731245425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220574295201739287820830283 330861442802608931731245425)
            ·
              refine ⟨248146082101956698798434069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 330861442802608931731245425 248146082101956698798434069)
              ·
                refine ⟨11631847598529220256176597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 248146082101956698798434069 11631847598529220256176597)
                ·
                  refine ⟨272621428090528599754139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11631847598529220256176597 272621428090528599754139)
                  ·
                    rfl

theorem cell23_4778355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 7].length) (baseStart_4778355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778355 prefixEnd_4778355 := by exact prefixLift 4778355
  have htrace : WordTrace (prefixWord ++ tailWord_4778355) baseStart_4778355 baseEnd_4778355 := by
    simpa [prefixWord, tailWord_4778355, baseEnd_4778355] using wordTrace_append hprefix tailTrace_4778355
  have hstable : (prefixWord ++ tailWord_4778355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778355).length < 2 ^ (prefixWord ++ tailWord_4778355).sum := by decide
  have hdescent : baseEnd_4778355 < baseStart_4778355 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778370 : List Nat := [3, 4, 2, 1, 2, 1, 1, 3, 1, 3, 2]
def baseStart_4778370 : Nat := 118140960795 + 4778370 * 2 ^ 59
def prefixEnd_4778370 : Nat := 4983230072969 + 3 ^ 40 * 4778370 * 2
def baseEnd_4778370 : Nat := 2453600555024574839099683

theorem tailTrace_4778370 : CollatzResearch.WordTrace tailWord_4778370 prefixEnd_4778370 2453600555024574839099683 := by
  unfold tailWord_4778370
  simp only [CollatzResearch.WordTrace]
  refine ⟨43570367924697261367403141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116187647799192696979741709 43570367924697261367403141)
  ·
    refine ⟨8169443985880736506388089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43570367924697261367403141 8169443985880736506388089)
    ·
      refine ⟨6127082989410552379791067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8169443985880736506388089 6127082989410552379791067)
      ·
        refine ⟨9190624484115828569686601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6127082989410552379791067 9190624484115828569686601)
        ·
          refine ⟨6892968363086871427264951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9190624484115828569686601 6892968363086871427264951)
          ·
            refine ⟨10339452544630307140897427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6892968363086871427264951 10339452544630307140897427)
            ·
              refine ⟨15509178816945460711346141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10339452544630307140897427 15509178816945460711346141)
              ·
                refine ⟨5815942056354547766754803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15509178816945460711346141 5815942056354547766754803)
                ·
                  refine ⟨8723913084531821650132205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5815942056354547766754803 8723913084531821650132205)
                  ·
                    refine ⟨3271467406699433118799577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8723913084531821650132205 3271467406699433118799577)
                    ·
                      refine ⟨2453600555024574839099683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3271467406699433118799577 2453600555024574839099683)
                      ·
                        rfl

theorem cell23_4778370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_4778370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778370 prefixEnd_4778370 := by exact prefixLift 4778370
  have htrace : WordTrace (prefixWord ++ tailWord_4778370) baseStart_4778370 baseEnd_4778370 := by
    simpa [prefixWord, tailWord_4778370, baseEnd_4778370] using wordTrace_append hprefix tailTrace_4778370
  have hstable : (prefixWord ++ tailWord_4778370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778370).length < 2 ^ (prefixWord ++ tailWord_4778370).sum := by decide
  have hdescent : baseEnd_4778370 < baseStart_4778370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778385 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 5, 7]
def baseStart_4778385 : Nat := 118140960795 + 4778385 * 2 ^ 59
def prefixEnd_4778385 : Nat := 4983230072969 + 3 ^ 40 * 4778385 * 2
def baseEnd_4778385 : Nat := 817869419078130760137371

theorem tailTrace_4778385 : CollatzResearch.WordTrace tailWord_4778385 prefixEnd_4778385 817869419078130760137371 := by
  unfold tailWord_4778385
  simp only [CollatzResearch.WordTrace]
  refine ⟨174282018793734703031408609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116188012529156468687605739 174282018793734703031408609)
  ·
    refine ⟨130711514095301027273556457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174282018793734703031408609 130711514095301027273556457)
    ·
      refine ⟨98033635571475770455167343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130711514095301027273556457 98033635571475770455167343)
      ·
        refine ⟨147050453357213655682751015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98033635571475770455167343 147050453357213655682751015)
        ·
          refine ⟨220575680035820483524126523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147050453357213655682751015 220575680035820483524126523)
          ·
            refine ⟨330863520053730725286189785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220575680035820483524126523 330863520053730725286189785)
            ·
              refine ⟨248147640040298043964642339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 330863520053730725286189785 248147640040298043964642339)
              ·
                refine ⟨372221460060447065946963509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 248147640040298043964642339 372221460060447065946963509)
                ·
                  refine ⟨34895761880666912432527829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 372221460060447065946963509 34895761880666912432527829)
                  ·
                    refine ⟨817869419078130760137371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34895761880666912432527829 817869419078130760137371)
                    ·
                      rfl

theorem cell23_4778385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 7].length) (baseStart_4778385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778385 prefixEnd_4778385 := by exact prefixLift 4778385
  have htrace : WordTrace (prefixWord ++ tailWord_4778385) baseStart_4778385 baseEnd_4778385 := by
    simpa [prefixWord, tailWord_4778385, baseEnd_4778385] using wordTrace_append hprefix tailTrace_4778385
  have hstable : (prefixWord ++ tailWord_4778385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778385).length < 2 ^ (prefixWord ++ tailWord_4778385).sum := by decide
  have hdescent : baseEnd_4778385 < baseStart_4778385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778402 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 3, 7]
def baseStart_4778402 : Nat := 118140960795 + 4778402 * 2 ^ 59
def prefixEnd_4778402 : Nat := 4983230072969 + 3 ^ 40 * 4778402 * 2
def baseEnd_4778402 : Nat := 817872328801839571299845

theorem tailTrace_4778402 : CollatzResearch.WordTrace tailWord_4778402 prefixEnd_4778402 817872328801839571299845 := by
  unfold tailWord_4778402
  simp only [CollatzResearch.WordTrace]
  refine ⟨43570659708668278733694365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116188425889782076623184973 43570659708668278733694365)
  ·
    refine ⟨16338997390750604525135387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43570659708668278733694365 16338997390750604525135387)
    ·
      refine ⟨24508496086125906787703081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16338997390750604525135387 24508496086125906787703081)
      ·
        refine ⟨18381372064594430090777311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24508496086125906787703081 18381372064594430090777311)
        ·
          refine ⟨27572058096891645136165967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18381372064594430090777311 27572058096891645136165967)
          ·
            refine ⟨41358087145337467704248951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27572058096891645136165967 41358087145337467704248951)
            ·
              refine ⟨62037130718006201556373427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41358087145337467704248951 62037130718006201556373427)
              ·
                refine ⟨93055696077009302334560141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62037130718006201556373427 93055696077009302334560141)
                ·
                  refine ⟨34895886028878488375460053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93055696077009302334560141 34895886028878488375460053)
                  ·
                    refine ⟨817872328801839571299845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34895886028878488375460053 817872328801839571299845)
                    ·
                      rfl

theorem cell23_4778402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_4778402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778402 prefixEnd_4778402 := by exact prefixLift 4778402
  have htrace : WordTrace (prefixWord ++ tailWord_4778402) baseStart_4778402 baseEnd_4778402 := by
    simpa [prefixWord, tailWord_4778402, baseEnd_4778402] using wordTrace_append hprefix tailTrace_4778402
  have hstable : (prefixWord ++ tailWord_4778402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778402).length < 2 ^ (prefixWord ++ tailWord_4778402).sum := by decide
  have hdescent : baseEnd_4778402 < baseStart_4778402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778436 : List Nat := [2, 3, 3, 2, 2, 1, 1, 2, 2, 5]
def baseStart_4778436 : Nat := 118140960795 + 4778436 * 2 ^ 59
def prefixEnd_4778436 : Nat := 4983230072969 + 3 ^ 40 * 4778436 * 2
def baseEnd_4778436 : Nat := 817878148249257193624793

theorem tailTrace_4778436 : CollatzResearch.WordTrace tailWord_4778436 prefixEnd_4778436 817878148249257193624793 := by
  unfold tailWord_4778436
  simp only [CollatzResearch.WordTrace]
  refine ⟨87141939458274969370757581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116189252611033292494343441 87141939458274969370757581)
  ·
    refine ⟨32678227296853113514034093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87141939458274969370757581 32678227296853113514034093)
    ·
      refine ⟨12254335236319917567762785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32678227296853113514034093 12254335236319917567762785)
      ·
        refine ⟨9190751427239938175822089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12254335236319917567762785 9190751427239938175822089)
        ·
          refine ⟨6893063570429953631866567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9190751427239938175822089 6893063570429953631866567)
          ·
            refine ⟨10339595355644930447799851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6893063570429953631866567 10339595355644930447799851)
            ·
              refine ⟨15509393033467395671699777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10339595355644930447799851 15509393033467395671699777)
              ·
                refine ⟨11632044775100546753774833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15509393033467395671699777 11632044775100546753774833)
                ·
                  refine ⟨8724033581325410065331125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11632044775100546753774833 8724033581325410065331125)
                  ·
                    refine ⟨817878148249257193624793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8724033581325410065331125 817878148249257193624793)
                    ·
                      rfl

theorem cell23_4778436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_4778436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778436 prefixEnd_4778436 := by exact prefixLift 4778436
  have htrace : WordTrace (prefixWord ++ tailWord_4778436) baseStart_4778436 baseEnd_4778436 := by
    simpa [prefixWord, tailWord_4778436, baseEnd_4778436] using wordTrace_append hprefix tailTrace_4778436
  have hstable : (prefixWord ++ tailWord_4778436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778436).length < 2 ^ (prefixWord ++ tailWord_4778436).sum := by decide
  have hdescent : baseEnd_4778436 < baseStart_4778436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778439 : List Nat := [1, 1, 4, 1, 1, 5, 1, 2, 2, 1, 4]
def baseStart_4778439 : Nat := 118140960795 + 4778439 * 2 ^ 59
def prefixEnd_4778439 : Nat := 4983230072969 + 3 ^ 40 * 4778439 * 2
def baseEnd_4778439 : Nat := 2453635985189735069136865

theorem tailTrace_4778439 : CollatzResearch.WordTrace tailWord_4778439 prefixEnd_4778439 2453635985189735069136865 := by
  unfold tailWord_4778439
  simp only [CollatzResearch.WordTrace]
  refine ⟨174283988335539070253874371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116189325557026046835916247 174283988335539070253874371)
  ·
    refine ⟨261425982503308605380811557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174283988335539070253874371 261425982503308605380811557)
    ·
      refine ⟨49017371719370363508902167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 261425982503308605380811557 49017371719370363508902167)
      ·
        refine ⟨73526057579055545263353251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49017371719370363508902167 73526057579055545263353251)
        ·
          refine ⟨110289086368583317895029877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73526057579055545263353251 110289086368583317895029877)
          ·
            refine ⟨10339601847054686052659051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 110289086368583317895029877 10339601847054686052659051)
            ·
              refine ⟨15509402770582029078988577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10339601847054686052659051 15509402770582029078988577)
              ·
                refine ⟨11632052077936521809241433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15509402770582029078988577 11632052077936521809241433)
                ·
                  refine ⟨8724039058452391356931075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11632052077936521809241433 8724039058452391356931075)
                  ·
                    refine ⟨13086058587678587035396613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8724039058452391356931075 13086058587678587035396613)
                    ·
                      refine ⟨2453635985189735069136865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13086058587678587035396613 2453635985189735069136865)
                      ·
                        rfl

theorem cell23_4778439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_4778439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778439 prefixEnd_4778439 := by exact prefixLift 4778439
  have htrace : WordTrace (prefixWord ++ tailWord_4778439) baseStart_4778439 baseEnd_4778439 := by
    simpa [prefixWord, tailWord_4778439, baseEnd_4778439] using wordTrace_append hprefix tailTrace_4778439
  have hstable : (prefixWord ++ tailWord_4778439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778439).length < 2 ^ (prefixWord ++ tailWord_4778439).sum := by decide
  have hdescent : baseEnd_4778439 < baseStart_4778439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778500 : List Nat := [2, 3, 2, 3, 1, 1, 4, 2, 1, 4]
def baseStart_4778500 : Nat := 118140960795 + 4778500 * 2 ^ 59
def prefixEnd_4778500 : Nat := 4983230072969 + 3 ^ 40 * 4778500 * 2
def baseEnd_4778500 : Nat := 817889102503219776824695

theorem tailTrace_4778500 : CollatzResearch.WordTrace tailWord_4778500 prefixEnd_4778500 817889102503219776824695 := by
  unfold tailWord_4778500
  simp only [CollatzResearch.WordTrace]
  refine ⟨87143106594159038835922477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116190808792212051781229969 87143106594159038835922477)
  ·
    refine ⟨32678664972809639563470929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87143106594159038835922477 32678664972809639563470929)
    ·
      refine ⟨24508998729607229672603197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32678664972809639563470929 24508998729607229672603197)
      ·
        refine ⟨9190874523602711127226199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24508998729607229672603197 9190874523602711127226199)
        ·
          refine ⟨13786311785404066690839299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9190874523602711127226199 13786311785404066690839299)
          ·
            refine ⟨20679467678106100036258949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13786311785404066690839299 20679467678106100036258949)
            ·
              refine ⟨3877400189644893756798553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20679467678106100036258949 3877400189644893756798553)
              ·
                refine ⟨2908050142233670317598915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3877400189644893756798553 2908050142233670317598915)
                ·
                  refine ⟨4362075213350505476398373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2908050142233670317598915 4362075213350505476398373)
                  ·
                    refine ⟨817889102503219776824695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4362075213350505476398373 817889102503219776824695)
                    ·
                      rfl

theorem cell23_4778500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_4778500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778500 prefixEnd_4778500 := by exact prefixLift 4778500
  have htrace : WordTrace (prefixWord ++ tailWord_4778500) baseStart_4778500 baseEnd_4778500 := by
    simpa [prefixWord, tailWord_4778500, baseEnd_4778500] using wordTrace_append hprefix tailTrace_4778500
  have hstable : (prefixWord ++ tailWord_4778500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778500).length < 2 ^ (prefixWord ++ tailWord_4778500).sum := by decide
  have hdescent : baseEnd_4778500 < baseStart_4778500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778506 : List Nat := [3, 1, 2, 2, 2, 1, 2, 3, 3, 1, 3]
def baseStart_4778506 : Nat := 118140960795 + 4778506 * 2 ^ 59
def prefixEnd_4778506 : Nat := 4983230072969 + 3 ^ 40 * 4778506 * 2
def baseEnd_4778506 : Nat := 2453670388393586306999057

theorem tailTrace_4778506 : CollatzResearch.WordTrace tailWord_4778506 prefixEnd_4778506 2453670388393586306999057 := by
  unfold tailWord_4778506
  simp only [CollatzResearch.WordTrace]
  refine ⟨43571608006574085174140843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116190954684197560464375581 43571608006574085174140843)
  ·
    refine ⟨65357412009861127761211265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43571608006574085174140843 65357412009861127761211265)
    ·
      refine ⟨49018059007395845820908449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65357412009861127761211265 49018059007395845820908449)
      ·
        refine ⟨36763544255546884365681337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49018059007395845820908449 36763544255546884365681337)
        ·
          refine ⟨27572658191660163274261003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36763544255546884365681337 27572658191660163274261003)
          ·
            refine ⟨41358987287490244911391505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27572658191660163274261003 41358987287490244911391505)
            ·
              refine ⟨31019240465617683683543629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41358987287490244911391505 31019240465617683683543629)
              ·
                refine ⟨11632215174606631381328861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31019240465617683683543629 11632215174606631381328861)
                ·
                  refine ⟨4362080690477486767998323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11632215174606631381328861 4362080690477486767998323)
                  ·
                    refine ⟨6543121035716230151997485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4362080690477486767998323 6543121035716230151997485)
                    ·
                      refine ⟨2453670388393586306999057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6543121035716230151997485 2453670388393586306999057)
                      ·
                        rfl

theorem cell23_4778506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_4778506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778506 prefixEnd_4778506 := by exact prefixLift 4778506
  have htrace : WordTrace (prefixWord ++ tailWord_4778506) baseStart_4778506 baseEnd_4778506 := by
    simpa [prefixWord, tailWord_4778506, baseEnd_4778506] using wordTrace_append hprefix tailTrace_4778506
  have hstable : (prefixWord ++ tailWord_4778506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778506).length < 2 ^ (prefixWord ++ tailWord_4778506).sum := by decide
  have hdescent : baseEnd_4778506 < baseStart_4778506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778529 : List Nat := [1, 2, 3, 2, 2, 1, 1, 3, 3, 1, 4]
def baseStart_4778529 : Nat := 118140960795 + 4778529 * 2 ^ 59
def prefixEnd_4778529 : Nat := 4983230072969 + 3 ^ 40 * 4778529 * 2
def baseEnd_4778529 : Nat := 2453682198448639717011451

theorem tailTrace_4778529 : CollatzResearch.WordTrace tailWord_4778529 prefixEnd_4778529 2453682198448639717011451 := by
  unfold tailWord_4778529
  simp only [CollatzResearch.WordTrace]
  refine ⟨174287270905213015624650641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116191513936808677083100427 174287270905213015624650641)
  ·
    refine ⟨130715453178909761718487981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174287270905213015624650641 130715453178909761718487981)
    ·
      refine ⟨49018294942091160644432993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130715453178909761718487981 49018294942091160644432993)
      ·
        refine ⟨36763721206568370483324745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49018294942091160644432993 36763721206568370483324745)
        ·
          refine ⟨27572790904926277862493559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36763721206568370483324745 27572790904926277862493559)
          ·
            refine ⟨41359186357389416793740339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27572790904926277862493559 41359186357389416793740339)
            ·
              refine ⟨62038779536084125190610509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41359186357389416793740339 62038779536084125190610509)
              ·
                refine ⟨23264542326031546946478941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62038779536084125190610509 23264542326031546946478941)
                ·
                  refine ⟨8724203372261830104929603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23264542326031546946478941 8724203372261830104929603)
                  ·
                    refine ⟨13086305058392745157394405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8724203372261830104929603 13086305058392745157394405)
                    ·
                      refine ⟨2453682198448639717011451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13086305058392745157394405 2453682198448639717011451)
                      ·
                        rfl

theorem cell23_4778529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_4778529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778529 prefixEnd_4778529 := by exact prefixLift 4778529
  have htrace : WordTrace (prefixWord ++ tailWord_4778529) baseStart_4778529 baseEnd_4778529 := by
    simpa [prefixWord, tailWord_4778529, baseEnd_4778529] using wordTrace_append hprefix tailTrace_4778529
  have hstable : (prefixWord ++ tailWord_4778529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778529).length < 2 ^ (prefixWord ++ tailWord_4778529).sum := by decide
  have hdescent : baseEnd_4778529 < baseStart_4778529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778549 : List Nat := [1, 3, 3, 1, 1, 2, 2, 3, 1, 1, 5]
def baseStart_4778549 : Nat := 118140960795 + 4778549 * 2 ^ 59
def prefixEnd_4778549 : Nat := 4983230072969 + 3 ^ 40 * 4778549 * 2
def baseEnd_4778549 : Nat := 2453692468061729638761359

theorem tailTrace_4778549 : CollatzResearch.WordTrace tailWord_4778549 prefixEnd_4778549 2453692468061729638761359 := by
  unfold tailWord_4778549
  simp only [CollatzResearch.WordTrace]
  refine ⟨174288000365140559040378701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116192000243427039360252467 174288000365140559040378701)
  ·
    refine ⟨65358000136927709640142013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174288000365140559040378701 65358000136927709640142013)
    ·
      refine ⟨24509250051347891115053255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65358000136927709640142013 24509250051347891115053255)
      ·
        refine ⟨36763875077021836672579883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24509250051347891115053255 36763875077021836672579883)
        ·
          refine ⟨55145812615532755008869825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36763875077021836672579883 55145812615532755008869825)
          ·
            refine ⟨41359359461649566256652369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55145812615532755008869825 41359359461649566256652369)
            ·
              refine ⟨31019519596237174692489277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41359359461649566256652369 31019519596237174692489277)
              ·
                refine ⟨11632319848588940509683479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31019519596237174692489277 11632319848588940509683479)
                ·
                  refine ⟨17448479772883410764525219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11632319848588940509683479 17448479772883410764525219)
                  ·
                    refine ⟨26172719659325116146787829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17448479772883410764525219 26172719659325116146787829)
                    ·
                      refine ⟨2453692468061729638761359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26172719659325116146787829 2453692468061729638761359)
                      ·
                        rfl

theorem cell23_4778549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_4778549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778549 prefixEnd_4778549 := by exact prefixLift 4778549
  have htrace : WordTrace (prefixWord ++ tailWord_4778549) baseStart_4778549 baseEnd_4778549 := by
    simpa [prefixWord, tailWord_4778549, baseEnd_4778549] using wordTrace_append hprefix tailTrace_4778549
  have hstable : (prefixWord ++ tailWord_4778549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778549).length < 2 ^ (prefixWord ++ tailWord_4778549).sum := by decide
  have hdescent : baseEnd_4778549 < baseStart_4778549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778552 : List Nat := [2, 1, 2, 1, 4, 1, 12]
def baseStart_4778552 : Nat := 118140960795 + 4778552 * 2 ^ 59
def prefixEnd_4778552 : Nat := 4983230072969 + 3 ^ 40 * 4778552 * 2
def baseEnd_4778552 : Nat := 30292518623502384284245

theorem tailTrace_4778552 : CollatzResearch.WordTrace tailWord_4778552 prefixEnd_4778552 30292518623502384284245 := by
  unfold tailWord_4778552
  simp only [CollatzResearch.WordTrace]
  refine ⟨87144054892064845276368955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116192073189419793701825273 87144054892064845276368955)
  ·
    refine ⟨130716082338097267914553433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87144054892064845276368955 130716082338097267914553433)
    ·
      refine ⟨98037061753572950935915075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130716082338097267914553433 98037061753572950935915075)
      ·
        refine ⟨147055592630359426403872613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98037061753572950935915075 147055592630359426403872613)
        ·
          refine ⟨27572923618192392450726115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 147055592630359426403872613 27572923618192392450726115)
          ·
            refine ⟨41359385427288588676089173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27572923618192392450726115 41359385427288588676089173)
            ·
              refine ⟨30292518623502384284245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 41359385427288588676089173 30292518623502384284245)
              ·
                rfl

theorem cell23_4778552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 12].length) (baseStart_4778552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778552 prefixEnd_4778552 := by exact prefixLift 4778552
  have htrace : WordTrace (prefixWord ++ tailWord_4778552) baseStart_4778552 baseEnd_4778552 := by
    simpa [prefixWord, tailWord_4778552, baseEnd_4778552] using wordTrace_append hprefix tailTrace_4778552
  have hstable : (prefixWord ++ tailWord_4778552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778552).length < 2 ^ (prefixWord ++ tailWord_4778552).sum := by decide
  have hdescent : baseEnd_4778552 < baseStart_4778552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778556 : List Nat := [2, 2, 2, 2, 3, 2, 1, 1, 4, 4]
def baseStart_4778556 : Nat := 118140960795 + 4778556 * 2 ^ 59
def prefixEnd_4778556 : Nat := 4983230072969 + 3 ^ 40 * 4778556 * 2
def baseEnd_4778556 : Nat := 817898687475437037124609

theorem tailTrace_4778556 : CollatzResearch.WordTrace tailWord_4778556 prefixEnd_4778556 817898687475437037124609 := by
  unfold tailWord_4778556
  simp only [CollatzResearch.WordTrace]
  refine ⟨87144127838057599617941761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116192170450743466157255681 87144127838057599617941761)
  ·
    refine ⟨65358095878543199713456321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87144127838057599617941761 65358095878543199713456321)
    ·
      refine ⟨49018571908907399785092241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65358095878543199713456321 49018571908907399785092241)
      ·
        refine ⟨36763928931680549838819181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49018571908907399785092241 36763928931680549838819181)
        ·
          refine ⟨13786473349380206189557193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36763928931680549838819181 13786473349380206189557193)
          ·
            refine ⟨10339855012035154642167895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13786473349380206189557193 10339855012035154642167895)
            ·
              refine ⟨15509782518052731963251843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10339855012035154642167895 15509782518052731963251843)
              ·
                refine ⟨23264673777079097944877765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15509782518052731963251843 23264673777079097944877765)
                ·
                  refine ⟨4362126333202330864664581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23264673777079097944877765 4362126333202330864664581)
                  ·
                    refine ⟨817898687475437037124609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4362126333202330864664581 817898687475437037124609)
                    ·
                      rfl

theorem cell23_4778556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 4, 4].length) (baseStart_4778556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778556 prefixEnd_4778556 := by exact prefixLift 4778556
  have htrace : WordTrace (prefixWord ++ tailWord_4778556) baseStart_4778556 baseEnd_4778556 := by
    simpa [prefixWord, tailWord_4778556, baseEnd_4778556] using wordTrace_append hprefix tailTrace_4778556
  have hstable : (prefixWord ++ tailWord_4778556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778556).length < 2 ^ (prefixWord ++ tailWord_4778556).sum := by decide
  have hdescent : baseEnd_4778556 < baseStart_4778556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778573 : List Nat := [1, 6, 1, 1, 2, 3, 1, 1, 1, 6]
def baseStart_4778573 : Nat := 118140960795 + 4778573 * 2 ^ 59
def prefixEnd_4778573 : Nat := 4983230072969 + 3 ^ 40 * 4778573 * 2
def baseEnd_4778573 : Nat := 817901597199145848287083

theorem tailTrace_4778573 : CollatzResearch.WordTrace tailWord_4778573 prefixEnd_4778573 817901597199145848287083 := by
  unfold tailWord_4778573
  simp only [CollatzResearch.WordTrace]
  refine ⟨174288875717053611139252373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116192583811369074092834915 174288875717053611139252373)
  ·
    refine ⟨8169791049236888022152455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 174288875717053611139252373 8169791049236888022152455)
    ·
      refine ⟨12254686573855332033228683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8169791049236888022152455 12254686573855332033228683)
      ·
        refine ⟨18382029860782998049843025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12254686573855332033228683 18382029860782998049843025)
        ·
          refine ⟨13786522395587248537382269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18382029860782998049843025 13786522395587248537382269)
          ·
            refine ⟨5169945898345218201518351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13786522395587248537382269 5169945898345218201518351)
            ·
              refine ⟨7754918847517827302277527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5169945898345218201518351 7754918847517827302277527)
              ·
                refine ⟨11632378271276740953416291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7754918847517827302277527 11632378271276740953416291)
                ·
                  refine ⟨17448567406915111430124437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11632378271276740953416291 17448567406915111430124437)
                  ·
                    refine ⟨817901597199145848287083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17448567406915111430124437 817901597199145848287083)
                    ·
                      rfl

theorem cell23_4778573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_4778573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778573 prefixEnd_4778573 := by exact prefixLift 4778573
  have htrace : WordTrace (prefixWord ++ tailWord_4778573) baseStart_4778573 baseEnd_4778573 := by
    simpa [prefixWord, tailWord_4778573, baseEnd_4778573] using wordTrace_append hprefix tailTrace_4778573
  have hstable : (prefixWord ++ tailWord_4778573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778573).length < 2 ^ (prefixWord ++ tailWord_4778573).sum := by decide
  have hdescent : baseEnd_4778573 < baseStart_4778573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778596 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3]
def baseStart_4778596 : Nat := 118140960795 + 4778596 * 2 ^ 59
def prefixEnd_4778596 : Nat := 4983230072969 + 3 ^ 40 * 4778596 * 2
def baseEnd_4778596 : Nat := 2453716601652490954873643

theorem tailTrace_4778596 : CollatzResearch.WordTrace tailWord_4778596 prefixEnd_4778596 2453716601652490954873643 := by
  unfold tailWord_4778596
  simp only [CollatzResearch.WordTrace]
  refine ⟨87144857297985143033669821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116193143063980190711559761 87144857297985143033669821)
  ·
    refine ⟨32679321486744428637626183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87144857297985143033669821 32679321486744428637626183)
    ·
      refine ⟨49018982230116642956439275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32679321486744428637626183 49018982230116642956439275)
      ·
        refine ⟨73528473345174964434658913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49018982230116642956439275 73528473345174964434658913)
        ·
          refine ⟨55146355008881223325994185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73528473345174964434658913 55146355008881223325994185)
          ·
            refine ⟨41359766256660917494495639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55146355008881223325994185 41359766256660917494495639)
            ·
              refine ⟨62039649384991376241743459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41359766256660917494495639 62039649384991376241743459)
              ·
                refine ⟨93059474077487064362615189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62039649384991376241743459 93059474077487064362615189)
                ·
                  refine ⟨4362162847382206141997587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 93059474077487064362615189 4362162847382206141997587)
                  ·
                    refine ⟨6543244271073309212996381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4362162847382206141997587 6543244271073309212996381)
                    ·
                      refine ⟨2453716601652490954873643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6543244271073309212996381 2453716601652490954873643)
                      ·
                        rfl

theorem cell23_4778596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3].length) (baseStart_4778596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778596 prefixEnd_4778596 := by exact prefixLift 4778596
  have htrace : WordTrace (prefixWord ++ tailWord_4778596) baseStart_4778596 baseEnd_4778596 := by
    simpa [prefixWord, tailWord_4778596, baseEnd_4778596] using wordTrace_append hprefix tailTrace_4778596
  have hstable : (prefixWord ++ tailWord_4778596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778596).length < 2 ^ (prefixWord ++ tailWord_4778596).sum := by decide
  have hdescent : baseEnd_4778596 < baseStart_4778596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778614 : List Nat := [5, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2]
def baseStart_4778614 : Nat := 118140960795 + 4778614 * 2 ^ 59
def prefixEnd_4778614 : Nat := 4983230072969 + 3 ^ 40 * 4778614 * 2
def baseEnd_4778614 : Nat := 2453725844304271884448561

theorem tailTrace_4778614 : CollatzResearch.WordTrace tailWord_4778614 prefixEnd_4778614 2453725844304271884448561 := by
  unfold tailWord_4778614
  simp only [CollatzResearch.WordTrace]
  refine ⟨10893148194369067196343431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116193580739936716760996597 10893148194369067196343431)
  ·
    refine ⟨16339722291553600794515147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10893148194369067196343431 16339722291553600794515147)
    ·
      refine ⟨24509583437330401191772721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16339722291553600794515147 24509583437330401191772721)
      ·
        refine ⟨18382187577997800893829541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24509583437330401191772721 18382187577997800893829541)
        ·
          refine ⟨3446660170874587667593039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18382187577997800893829541 3446660170874587667593039)
          ·
            refine ⟨5169990256311881501389559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3446660170874587667593039 5169990256311881501389559)
            ·
              refine ⟨7754985384467822252084339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5169990256311881501389559 7754985384467822252084339)
              ·
                refine ⟨11632478076701733378126509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7754985384467822252084339 11632478076701733378126509)
                ·
                  refine ⟨4362179278763150016797441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11632478076701733378126509 4362179278763150016797441)
                  ·
                    refine ⟨3271634459072362512598081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4362179278763150016797441 3271634459072362512598081)
                    ·
                      refine ⟨2453725844304271884448561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3271634459072362512598081 2453725844304271884448561)
                      ·
                        rfl

theorem cell23_4778614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_4778614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778614 prefixEnd_4778614 := by exact prefixLift 4778614
  have htrace : WordTrace (prefixWord ++ tailWord_4778614) baseStart_4778614 baseEnd_4778614 := by
    simpa [prefixWord, tailWord_4778614, baseEnd_4778614] using wordTrace_append hprefix tailTrace_4778614
  have hstable : (prefixWord ++ tailWord_4778614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778614).length < 2 ^ (prefixWord ++ tailWord_4778614).sum := by decide
  have hdescent : baseEnd_4778614 < baseStart_4778614 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778639 : List Nat := [1, 1, 2, 1, 1, 1, 1, 6, 2, 4, 3]
def baseStart_4778639 : Nat := 118140960795 + 4778639 * 2 ^ 59
def prefixEnd_4778639 : Nat := 4983230072969 + 3 ^ 40 * 4778639 * 2
def baseEnd_4778639 : Nat := 2453738681320634286635945

theorem tailTrace_4778639 : CollatzResearch.WordTrace tailWord_4778639 prefixEnd_4778639 2453738681320634286635945 := by
  unfold tailWord_4778639
  simp only [CollatzResearch.WordTrace]
  refine ⟨174291282934814504411154971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116194188623209669607436647 174291282934814504411154971)
  ·
    refine ⟨261436924402221756616732457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174291282934814504411154971 261436924402221756616732457)
    ·
      refine ⟨196077693301666317462549343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261436924402221756616732457 196077693301666317462549343)
      ·
        refine ⟨294116539952499476193824015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196077693301666317462549343 294116539952499476193824015)
        ·
          refine ⟨441174809928749214290736023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294116539952499476193824015 441174809928749214290736023)
          ·
            refine ⟨661762214893123821436104035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 441174809928749214290736023 661762214893123821436104035)
            ·
              refine ⟨992643322339685732154156053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 661762214893123821436104035 992643322339685732154156053)
              ·
                refine ⟨46530155734672768694726065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 992643322339685732154156053 46530155734672768694726065)
                ·
                  refine ⟨34897616801004576521044549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46530155734672768694726065 34897616801004576521044549)
                  ·
                    refine ⟨6543303150188358097695853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34897616801004576521044549 6543303150188358097695853)
                    ·
                      refine ⟨2453738681320634286635945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6543303150188358097695853 2453738681320634286635945)
                      ·
                        rfl

theorem cell23_4778639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 4, 3].length) (baseStart_4778639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778639 prefixEnd_4778639 := by exact prefixLift 4778639
  have htrace : WordTrace (prefixWord ++ tailWord_4778639) baseStart_4778639 baseEnd_4778639 := by
    simpa [prefixWord, tailWord_4778639, baseEnd_4778639] using wordTrace_append hprefix tailTrace_4778639
  have hstable : (prefixWord ++ tailWord_4778639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778639).length < 2 ^ (prefixWord ++ tailWord_4778639).sum := by decide
  have hdescent : baseEnd_4778639 < baseStart_4778639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778653 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 6, 2, 2]
def baseStart_4778653 : Nat := 118140960795 + 4778653 * 2 ^ 59
def prefixEnd_4778653 : Nat := 4983230072969 + 3 ^ 40 * 4778653 * 2
def baseEnd_4778653 : Nat := 2453745870049797231860881

theorem tailTrace_4778653 : CollatzResearch.WordTrace tailWord_4778653 prefixEnd_4778653 2453745870049797231860881 := by
  unfold tailWord_4778653
  simp only [CollatzResearch.WordTrace]
  refine ⟨174291793556763784802164613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116194529037842523201443075 174291793556763784802164613)
  ·
    refine ⟨32679711291893209650405865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174291793556763784802164613 32679711291893209650405865)
    ·
      refine ⟨24509783468919907237804399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32679711291893209650405865 24509783468919907237804399)
      ·
        refine ⟨36764675203379860856706599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24509783468919907237804399 36764675203379860856706599)
        ·
          refine ⟨55147012805069791285059899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36764675203379860856706599 55147012805069791285059899)
          ·
            refine ⟨82720519207604686927589849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55147012805069791285059899 82720519207604686927589849)
            ·
              refine ⟨62040389405703515195692387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82720519207604686927589849 62040389405703515195692387)
              ·
                refine ⟨93060584108555272793538581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62040389405703515195692387 93060584108555272793538581)
                ·
                  refine ⟨4362214880088528412197121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 93060584108555272793538581 4362214880088528412197121)
                  ·
                    refine ⟨3271661160066396309147841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4362214880088528412197121 3271661160066396309147841)
                    ·
                      refine ⟨2453745870049797231860881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3271661160066396309147841 2453745870049797231860881)
                      ·
                        rfl

theorem cell23_4778653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 6, 2, 2].length) (baseStart_4778653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778653 prefixEnd_4778653 := by exact prefixLift 4778653
  have htrace : WordTrace (prefixWord ++ tailWord_4778653) baseStart_4778653 baseEnd_4778653 := by
    simpa [prefixWord, tailWord_4778653, baseEnd_4778653] using wordTrace_append hprefix tailTrace_4778653
  have hstable : (prefixWord ++ tailWord_4778653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778653).length < 2 ^ (prefixWord ++ tailWord_4778653).sum := by decide
  have hdescent : baseEnd_4778653 < baseStart_4778653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778657 : List Nat := [1, 2, 3, 3, 3, 1, 3, 1, 1, 3, 2]
def baseStart_4778657 : Nat := 118140960795 + 4778657 * 2 ^ 59
def prefixEnd_4778657 : Nat := 4983230072969 + 3 ^ 40 * 4778657 * 2
def baseEnd_4778657 : Nat := 2453747923972415216210863

theorem tailTrace_4778657 : CollatzResearch.WordTrace tailWord_4778657 prefixEnd_4778657 2453747923972415216210863 := by
  unfold tailWord_4778657
  simp only [CollatzResearch.WordTrace]
  refine ⟨174291939448749293485310225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116194626299166195656873483 174291939448749293485310225)
  ·
    refine ⟨130718954586561970113982669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174291939448749293485310225 130718954586561970113982669)
    ·
      refine ⟨49019607969960738792743501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130718954586561970113982669 49019607969960738792743501)
      ·
        refine ⟨18382352988735277047278813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49019607969960738792743501 18382352988735277047278813)
        ·
          refine ⟨6893382370775728892729555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18382352988735277047278813 6893382370775728892729555)
          ·
            refine ⟨10340073556163593339094333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6893382370775728892729555 10340073556163593339094333)
            ·
              refine ⟨3877527583561347502160375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10340073556163593339094333 3877527583561347502160375)
              ·
                refine ⟨5816291375342021253240563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3877527583561347502160375 5816291375342021253240563)
                ·
                  refine ⟨8724437063013031879860845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5816291375342021253240563 8724437063013031879860845)
                  ·
                    refine ⟨3271663898629886954947817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8724437063013031879860845 3271663898629886954947817)
                    ·
                      refine ⟨2453747923972415216210863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3271663898629886954947817 2453747923972415216210863)
                      ·
                        rfl

theorem cell23_4778657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_4778657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778657 prefixEnd_4778657 := by exact prefixLift 4778657
  have htrace : WordTrace (prefixWord ++ tailWord_4778657) baseStart_4778657 baseEnd_4778657 := by
    simpa [prefixWord, tailWord_4778657, baseEnd_4778657] using wordTrace_append hprefix tailTrace_4778657
  have hstable : (prefixWord ++ tailWord_4778657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778657).length < 2 ^ (prefixWord ++ tailWord_4778657).sum := by decide
  have hdescent : baseEnd_4778657 < baseStart_4778657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778729 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 2, 3, 5]
def baseStart_4778729 : Nat := 118140960795 + 4778729 * 2 ^ 59
def prefixEnd_4778729 : Nat := 4983230072969 + 3 ^ 40 * 4778729 * 2
def baseEnd_4778729 : Nat := 2453784894579538934510531

theorem tailTrace_4778729 : CollatzResearch.WordTrace tailWord_4778729 prefixEnd_4778729 2453784894579538934510531 := by
  unfold tailWord_4778729
  simp only [CollatzResearch.WordTrace]
  refine ⟨174294565504488449781931241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116196377002992299854620827 174294565504488449781931241)
  ·
    refine ⟨130720924128366337336448431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174294565504488449781931241 130720924128366337336448431)
    ·
      refine ⟨196081386192549506004672647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130720924128366337336448431 196081386192549506004672647)
      ·
        refine ⟨294122079288824259007008971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196081386192549506004672647 294122079288824259007008971)
        ·
          refine ⟨441183118933236388510513457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294122079288824259007008971 441183118933236388510513457)
          ·
            refine ⟨330887339199927291382885093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 441183118933236388510513457 330887339199927291382885093)
            ·
              refine ⟨62041376099986367134290955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 330887339199927291382885093 62041376099986367134290955)
              ·
                refine ⟨93062064149979550701436433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62041376099986367134290955 93062064149979550701436433)
                ·
                  refine ⟨69796548112484663026077325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93062064149979550701436433 69796548112484663026077325)
                  ·
                    refine ⟨26173705542181748634778997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 69796548112484663026077325 26173705542181748634778997)
                    ·
                      refine ⟨2453784894579538934510531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26173705542181748634778997 2453784894579538934510531)
                      ·
                        rfl

theorem cell23_4778729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 3, 5].length) (baseStart_4778729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778729 prefixEnd_4778729 := by exact prefixLift 4778729
  have htrace : WordTrace (prefixWord ++ tailWord_4778729) baseStart_4778729 baseEnd_4778729 := by
    simpa [prefixWord, tailWord_4778729, baseEnd_4778729] using wordTrace_append hprefix tailTrace_4778729
  have hstable : (prefixWord ++ tailWord_4778729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778729).length < 2 ^ (prefixWord ++ tailWord_4778729).sum := by decide
  have hdescent : baseEnd_4778729 < baseStart_4778729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778739 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 6]
def baseStart_4778739 : Nat := 118140960795 + 4778739 * 2 ^ 59
def prefixEnd_4778739 : Nat := 4983230072969 + 3 ^ 40 * 4778739 * 2
def baseEnd_4778739 : Nat := 2453790029386083895385485

theorem tailTrace_4778739 : CollatzResearch.WordTrace tailWord_4778739 prefixEnd_4778739 2453790029386083895385485 := by
  unfold tailWord_4778739
  simp only [CollatzResearch.WordTrace]
  refine ⟨174294930234452221489795271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116196620156301480993196847 174294930234452221489795271)
  ·
    refine ⟨261442395351678332234692907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174294930234452221489795271 261442395351678332234692907)
    ·
      refine ⟨392163593027517498352039361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261442395351678332234692907 392163593027517498352039361)
      ·
        refine ⟨294122694770638123764029521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 392163593027517498352039361 294122694770638123764029521)
        ·
          refine ⟨220592021077978592823022141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 294122694770638123764029521 220592021077978592823022141)
          ·
            refine ⟨82722007904241972308633303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 220592021077978592823022141 82722007904241972308633303)
            ·
              refine ⟨124083011856362958462949955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82722007904241972308633303 124083011856362958462949955)
              ·
                refine ⟨186124517784544437694424933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124083011856362958462949955 186124517784544437694424933)
                ·
                  refine ⟨34898347084602082067704675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 186124517784544437694424933 34898347084602082067704675)
                  ·
                    refine ⟨52347520626903123101557013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34898347084602082067704675 52347520626903123101557013)
                    ·
                      refine ⟨2453790029386083895385485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52347520626903123101557013 2453790029386083895385485)
                      ·
                        rfl

theorem cell23_4778739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 6].length) (baseStart_4778739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778739 prefixEnd_4778739 := by exact prefixLift 4778739
  have htrace : WordTrace (prefixWord ++ tailWord_4778739) baseStart_4778739 baseEnd_4778739 := by
    simpa [prefixWord, tailWord_4778739, baseEnd_4778739] using wordTrace_append hprefix tailTrace_4778739
  have hstable : (prefixWord ++ tailWord_4778739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778739).length < 2 ^ (prefixWord ++ tailWord_4778739).sum := by decide
  have hdescent : baseEnd_4778739 < baseStart_4778739 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778746 : List Nat := [3, 1, 1, 1, 1, 3, 3, 2, 1, 4, 3]
def baseStart_4778746 : Nat := 118140960795 + 4778746 * 2 ^ 59
def prefixEnd_4778746 : Nat := 4983230072969 + 3 ^ 40 * 4778746 * 2
def baseEnd_4778746 : Nat := 2453793623750665367997953

theorem tailTrace_4778746 : CollatzResearch.WordTrace tailWord_4778746 prefixEnd_4778746 2453793623750665367997953 := by
  unfold tailWord_4778746
  simp only [CollatzResearch.WordTrace]
  refine ⟨43573796386356715421325023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116196790363617907790200061 43573796386356715421325023)
  ·
    refine ⟨65360694579535073131987535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43573796386356715421325023 65360694579535073131987535)
    ·
      refine ⟨98041041869302609697981303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65360694579535073131987535 98041041869302609697981303)
      ·
        refine ⟨147061562803953914546971955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98041041869302609697981303 147061562803953914546971955)
        ·
          refine ⟨220592344205930871820457933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147061562803953914546971955 220592344205930871820457933)
          ·
            refine ⟨82722129077224076932671725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 220592344205930871820457933 82722129077224076932671725)
            ·
              refine ⟨31020798403959028849751897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82722129077224076932671725 31020798403959028849751897)
              ·
                refine ⟨23265598802969271637313923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31020798403959028849751897 23265598802969271637313923)
                ·
                  refine ⟨34898398204453907455970885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23265598802969271637313923 34898398204453907455970885)
                  ·
                    refine ⟨6543449663335107647994541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34898398204453907455970885 6543449663335107647994541)
                    ·
                      refine ⟨2453793623750665367997953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6543449663335107647994541 2453793623750665367997953)
                      ·
                        rfl

theorem cell23_4778746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 1, 4, 3].length) (baseStart_4778746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778746 prefixEnd_4778746 := by exact prefixLift 4778746
  have htrace : WordTrace (prefixWord ++ tailWord_4778746) baseStart_4778746 baseEnd_4778746 := by
    simpa [prefixWord, tailWord_4778746, baseEnd_4778746] using wordTrace_append hprefix tailTrace_4778746
  have hstable : (prefixWord ++ tailWord_4778746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778746).length < 2 ^ (prefixWord ++ tailWord_4778746).sum := by decide
  have hdescent : baseEnd_4778746 < baseStart_4778746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778756 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 2, 4, 4]
def baseStart_4778756 : Nat := 118140960795 + 4778756 * 2 ^ 59
def prefixEnd_4778756 : Nat := 4983230072969 + 3 ^ 40 * 4778756 * 2
def baseEnd_4778756 : Nat := 2453798758557210328872907

theorem tailTrace_4778756 : CollatzResearch.WordTrace tailWord_4778756 prefixEnd_4778756 2453798758557210328872907 := by
  unfold tailWord_4778756
  simp only [CollatzResearch.WordTrace]
  refine ⟨87147775137695316696582061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116197033516927088928776081 87147775137695316696582061)
  ·
    refine ⟨32680415676635743761218273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87147775137695316696582061 32680415676635743761218273)
    ·
      refine ⟨24510311757476807820913705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32680415676635743761218273 24510311757476807820913705)
      ·
        refine ⟨18382733818107605865685279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24510311757476807820913705 18382733818107605865685279)
        ·
          refine ⟨27574100727161408798527919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18382733818107605865685279 27574100727161408798527919)
          ·
            refine ⟨41361151090742113197791879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27574100727161408798527919 41361151090742113197791879)
            ·
              refine ⟨62041726636113169796687819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41361151090742113197791879 62041726636113169796687819)
              ·
                refine ⟨93062589954169754695031729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62041726636113169796687819 93062589954169754695031729)
                ·
                  refine ⟨69796942465627316021273797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93062589954169754695031729 69796942465627316021273797)
                  ·
                    refine ⟨13086926712305121753988837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 69796942465627316021273797 13086926712305121753988837)
                    ·
                      refine ⟨2453798758557210328872907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13086926712305121753988837 2453798758557210328872907)
                      ·
                        rfl

theorem cell23_4778756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_4778756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778756 prefixEnd_4778756 := by exact prefixLift 4778756
  have htrace : WordTrace (prefixWord ++ tailWord_4778756) baseStart_4778756 baseEnd_4778756 := by
    simpa [prefixWord, tailWord_4778756, baseEnd_4778756] using wordTrace_append hprefix tailTrace_4778756
  have hstable : (prefixWord ++ tailWord_4778756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778756).length < 2 ^ (prefixWord ++ tailWord_4778756).sum := by decide
  have hdescent : baseEnd_4778756 < baseStart_4778756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778796 : List Nat := [2, 2, 1, 1, 1, 4, 2, 2, 3, 5]
def baseStart_4778796 : Nat := 118140960795 + 4778796 * 2 ^ 59
def prefixEnd_4778796 : Nat := 4983230072969 + 3 ^ 40 * 4778796 * 2
def baseEnd_4778796 : Nat := 817939765927796724124241

theorem tailTrace_4778796 : CollatzResearch.WordTrace tailWord_4778796 prefixEnd_4778796 817939765927796724124241 := by
  unfold tailWord_4778796
  simp only [CollatzResearch.WordTrace]
  refine ⟨87148504597622860112310121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116198006130163813483080161 87148504597622860112310121)
  ·
    refine ⟨65361378448217145084232591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87148504597622860112310121 65361378448217145084232591)
    ·
      refine ⟨98042067672325717626348887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65361378448217145084232591 98042067672325717626348887)
      ·
        refine ⟨147063101508488576439523331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98042067672325717626348887 147063101508488576439523331)
        ·
          refine ⟨220594652262732864659284997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147063101508488576439523331 220594652262732864659284997)
          ·
            refine ⟨41361497299262412123615937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 220594652262732864659284997 41361497299262412123615937)
            ·
              refine ⟨31021122974446809092711953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41361497299262412123615937 31021122974446809092711953)
              ·
                refine ⟨23265842230835106819533965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31021122974446809092711953 23265842230835106819533965)
                ·
                  refine ⟨8724690836563165057325237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23265842230835106819533965 8724690836563165057325237)
                  ·
                    refine ⟨817939765927796724124241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8724690836563165057325237 817939765927796724124241)
                    ·
                      rfl

theorem cell23_4778796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 5].length) (baseStart_4778796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778796 prefixEnd_4778796 := by exact prefixLift 4778796
  have htrace : WordTrace (prefixWord ++ tailWord_4778796) baseStart_4778796 baseEnd_4778796 := by
    simpa [prefixWord, tailWord_4778796, baseEnd_4778796] using wordTrace_append hprefix tailTrace_4778796
  have hstable : (prefixWord ++ tailWord_4778796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778796).length < 2 ^ (prefixWord ++ tailWord_4778796).sum := by decide
  have hdescent : baseEnd_4778796 < baseStart_4778796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778844 : List Nat := [2, 2, 4, 2, 1, 2, 1, 4, 1, 1, 3]
def baseStart_4778844 : Nat := 118140960795 + 4778844 * 2 ^ 59
def prefixEnd_4778844 : Nat := 4983230072969 + 3 ^ 40 * 4778844 * 2
def baseEnd_4778844 : Nat := 2453843944854805984572503

theorem tailTrace_4778844 : CollatzResearch.WordTrace tailWord_4778844 prefixEnd_4778844 2453843944854805984572503 := by
  unfold tailWord_4778844
  simp only [CollatzResearch.WordTrace]
  refine ⟨87149379949535912211183793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116199173266047882948245057 87149379949535912211183793)
  ·
    refine ⟨65362034962151934158387845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87149379949535912211183793 65362034962151934158387845)
    ·
      refine ⟨12255381555403487654697721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65362034962151934158387845 12255381555403487654697721)
      ·
        refine ⟨9191536166552615741023291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12255381555403487654697721 9191536166552615741023291)
        ·
          refine ⟨13787304249828923611534937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9191536166552615741023291 13787304249828923611534937)
          ·
            refine ⟨10340478187371692708651203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13787304249828923611534937 10340478187371692708651203)
            ·
              refine ⟨15510717281057539062976805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10340478187371692708651203 15510717281057539062976805)
              ·
                refine ⟨2908259490198288574308151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15510717281057539062976805 2908259490198288574308151)
                ·
                  refine ⟨4362389235297432861462227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2908259490198288574308151 4362389235297432861462227)
                  ·
                    refine ⟨6543583852946149292193341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4362389235297432861462227 6543583852946149292193341)
                    ·
                      refine ⟨2453843944854805984572503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6543583852946149292193341 2453843944854805984572503)
                      ·
                        rfl

theorem cell23_4778844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_4778844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778844 prefixEnd_4778844 := by exact prefixLift 4778844
  have htrace : WordTrace (prefixWord ++ tailWord_4778844) baseStart_4778844 baseEnd_4778844 := by
    simpa [prefixWord, tailWord_4778844, baseEnd_4778844] using wordTrace_append hprefix tailTrace_4778844
  have hstable : (prefixWord ++ tailWord_4778844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778844).length < 2 ^ (prefixWord ++ tailWord_4778844).sum := by decide
  have hdescent : baseEnd_4778844 < baseStart_4778844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778853 : List Nat := [1, 3, 1, 3, 1, 1, 3, 2, 3, 2, 3]
def baseStart_4778853 : Nat := 118140960795 + 4778853 * 2 ^ 59
def prefixEnd_4778853 : Nat := 4983230072969 + 3 ^ 40 * 4778853 * 2
def baseEnd_4778853 : Nat := 2453848566180696449359961

theorem tailTrace_4778853 : CollatzResearch.WordTrace tailWord_4778853 prefixEnd_4778853 2453848566180696449359961 := by
  unfold tailWord_4778853
  simp only [CollatzResearch.WordTrace]
  refine ⟨174299088156039218959445213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116199392104026145972963475 174299088156039218959445213)
  ·
    refine ⟨65362158058514707109791955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174299088156039218959445213 65362158058514707109791955)
    ·
      refine ⟨98043237087772060664687933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65362158058514707109791955 98043237087772060664687933)
      ·
        refine ⟨36766213907914522749257975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98043237087772060664687933 36766213907914522749257975)
        ·
          refine ⟨55149320861871784123886963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36766213907914522749257975 55149320861871784123886963)
          ·
            refine ⟨82723981292807676185830445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55149320861871784123886963 82723981292807676185830445)
            ·
              refine ⟨31021492984802878569686417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82723981292807676185830445 31021492984802878569686417)
              ·
                refine ⟨23266119738602158927264813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31021492984802878569686417 23266119738602158927264813)
                ·
                  refine ⟨8724794901975809597724305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23266119738602158927264813 8724794901975809597724305)
                  ·
                    refine ⟨6543596176481857198293229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8724794901975809597724305 6543596176481857198293229)
                    ·
                      refine ⟨2453848566180696449359961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6543596176481857198293229 2453848566180696449359961)
                      ·
                        rfl

theorem cell23_4778853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_4778853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778853 prefixEnd_4778853 := by exact prefixLift 4778853
  have htrace : WordTrace (prefixWord ++ tailWord_4778853) baseStart_4778853 baseEnd_4778853 := by
    simpa [prefixWord, tailWord_4778853, baseEnd_4778853] using wordTrace_append hprefix tailTrace_4778853
  have hstable : (prefixWord ++ tailWord_4778853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778853).length < 2 ^ (prefixWord ++ tailWord_4778853).sum := by decide
  have hdescent : baseEnd_4778853 < baseStart_4778853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778873 : List Nat := [1, 2, 1, 3, 2, 4, 3, 7]
def baseStart_4778873 : Nat := 118140960795 + 4778873 * 2 ^ 59
def prefixEnd_4778873 : Nat := 4983230072969 + 3 ^ 40 * 4778873 * 2
def baseEnd_4778873 : Nat := 90883660584955050781847

theorem tailTrace_4778873 : CollatzResearch.WordTrace tailWord_4778873 prefixEnd_4778873 90883660584955050781847 := by
  unfold tailWord_4778873
  simp only [CollatzResearch.WordTrace]
  refine ⟨174299817615966762375173273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116199878410644508250115515 174299817615966762375173273)
  ·
    refine ⟨130724863211975071781379955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174299817615966762375173273 130724863211975071781379955)
    ·
      refine ⟨196087294817962607672069933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130724863211975071781379955 196087294817962607672069933)
      ·
        refine ⟨73532735556735977877026225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196087294817962607672069933 73532735556735977877026225)
        ·
          refine ⟨55149551667551983407769669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73532735556735977877026225 55149551667551983407769669)
          ·
            refine ⟨10340540937665996888956813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55149551667551983407769669 10340540937665996888956813)
            ·
              refine ⟨3877702851624748833358805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10340540937665996888956813 3877702851624748833358805)
              ·
                refine ⟨90883660584955050781847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3877702851624748833358805 90883660584955050781847)
                ·
                  rfl

theorem cell23_4778873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 7].length) (baseStart_4778873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778873 prefixEnd_4778873 := by exact prefixLift 4778873
  have htrace : WordTrace (prefixWord ++ tailWord_4778873) baseStart_4778873 baseEnd_4778873 := by
    simpa [prefixWord, tailWord_4778873, baseEnd_4778873] using wordTrace_append hprefix tailTrace_4778873
  have hstable : (prefixWord ++ tailWord_4778873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778873).length < 2 ^ (prefixWord ++ tailWord_4778873).sum := by decide
  have hdescent : baseEnd_4778873 < baseStart_4778873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778883 : List Nat := [1, 1, 1, 3, 4, 1, 1, 4, 1, 3, 3]
def baseStart_4778883 : Nat := 118140960795 + 4778883 * 2 ^ 59
def prefixEnd_4778883 : Nat := 4983230072969 + 3 ^ 40 * 4778883 * 2
def baseEnd_4778883 : Nat := 2453863970600331331984823

theorem tailTrace_4778883 : CollatzResearch.WordTrace tailWord_4778883 prefixEnd_4778883 2453863970600331331984823 := by
  unfold tailWord_4778883
  simp only [CollatzResearch.WordTrace]
  refine ⟨174300182345930534083037303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116200121563953689388691535 174300182345930534083037303)
  ·
    refine ⟨261450273518895801124555955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174300182345930534083037303 261450273518895801124555955)
    ·
      refine ⟨392175410278343701686833933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261450273518895801124555955 392175410278343701686833933)
      ·
        refine ⟨147065778854378888132562725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 392175410278343701686833933 147065778854378888132562725)
        ·
          refine ⟨27574833535196041524855511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 147065778854378888132562725 27574833535196041524855511)
          ·
            refine ⟨41362250302794062287283267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27574833535196041524855511 41362250302794062287283267)
            ·
              refine ⟨62043375454191093430924901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41362250302794062287283267 62043375454191093430924901)
              ·
                refine ⟨11633132897660830018298419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62043375454191093430924901 11633132897660830018298419)
                ·
                  refine ⟨17449699346491245027447629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11633132897660830018298419 17449699346491245027447629)
                  ·
                    refine ⟨6543637254934216885292861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17449699346491245027447629 6543637254934216885292861)
                    ·
                      refine ⟨2453863970600331331984823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6543637254934216885292861 2453863970600331331984823)
                      ·
                        rfl

theorem cell23_4778883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 3, 3].length) (baseStart_4778883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778883 prefixEnd_4778883 := by exact prefixLift 4778883
  have htrace : WordTrace (prefixWord ++ tailWord_4778883) baseStart_4778883 baseEnd_4778883 := by
    simpa [prefixWord, tailWord_4778883, baseEnd_4778883] using wordTrace_append hprefix tailTrace_4778883
  have hstable : (prefixWord ++ tailWord_4778883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778883).length < 2 ^ (prefixWord ++ tailWord_4778883).sum := by decide
  have hdescent : baseEnd_4778883 < baseStart_4778883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4778887 : List Nat := [1, 1, 4, 2, 3, 1, 4, 1, 1, 2, 3]
def baseStart_4778887 : Nat := 118140960795 + 4778887 * 2 ^ 59
def prefixEnd_4778887 : Nat := 4983230072969 + 3 ^ 40 * 4778887 * 2
def baseEnd_4778887 : Nat := 2453866024522949316334805

theorem tailTrace_4778887 : CollatzResearch.WordTrace tailWord_4778887 prefixEnd_4778887 2453866024522949316334805 := by
  unfold tailWord_4778887
  simp only [CollatzResearch.WordTrace]
  refine ⟨174300328237916042766182915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116200218825277361844121943 174300328237916042766182915)
  ·
    refine ⟨261450492356874064149274373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174300328237916042766182915 261450492356874064149274373)
    ·
      refine ⟨49021967316913887027988945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 261450492356874064149274373 49021967316913887027988945)
      ·
        refine ⟨36766475487685415270991709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49021967316913887027988945 36766475487685415270991709)
        ·
          refine ⟨13787428307882030726621891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36766475487685415270991709 13787428307882030726621891)
          ·
            refine ⟨20681142461823046089932837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13787428307882030726621891 20681142461823046089932837)
            ·
              refine ⟨3877714211591821141862407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20681142461823046089932837 3877714211591821141862407)
              ·
                refine ⟨5816571317387731712793611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3877714211591821141862407 5816571317387731712793611)
                ·
                  refine ⟨8724856976081597569190417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5816571317387731712793611 8724856976081597569190417)
                  ·
                    refine ⟨6543642732061198176892813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8724856976081597569190417 6543642732061198176892813)
                    ·
                      refine ⟨2453866024522949316334805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6543642732061198176892813 2453866024522949316334805)
                      ·
                        rfl

theorem cell23_4778887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 1, 1, 2, 3].length) (baseStart_4778887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4778887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4778887 prefixEnd_4778887 := by exact prefixLift 4778887
  have htrace : WordTrace (prefixWord ++ tailWord_4778887) baseStart_4778887 baseEnd_4778887 := by
    simpa [prefixWord, tailWord_4778887, baseEnd_4778887] using wordTrace_append hprefix tailTrace_4778887
  have hstable : (prefixWord ++ tailWord_4778887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4778887).length < 2 ^ (prefixWord ++ tailWord_4778887).sum := by decide
  have hdescent : baseEnd_4778887 < baseStart_4778887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4778887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4779047 : List Nat := [1, 1, 7, 1, 1, 2, 1, 1, 1, 3, 4]
def baseStart_4779047 : Nat := 118140960795 + 4779047 * 2 ^ 59
def prefixEnd_4779047 : Nat := 4983230072969 + 3 ^ 40 * 4779047 * 2
def baseEnd_4779047 : Nat := 2453948181427668690334069

theorem tailTrace_4779047 : CollatzResearch.WordTrace tailWord_4779047 prefixEnd_4779047 2453948181427668690334069 := by
  unfold tailWord_4779047
  simp only [CollatzResearch.WordTrace]
  refine ⟨174306163917336390092007395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116204109278224260061338263 174306163917336390092007395)
  ·
    refine ⟨261459245876004585138011093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174306163917336390092007395 261459245876004585138011093)
    ·
      refine ⟨6127951075218857464172135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 261459245876004585138011093 6127951075218857464172135)
      ·
        refine ⟨9191926612828286196258203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6127951075218857464172135 9191926612828286196258203)
        ·
          refine ⟨13787889919242429294387305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9191926612828286196258203 13787889919242429294387305)
          ·
            refine ⟨10340917439431821970790479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13787889919242429294387305 10340917439431821970790479)
            ·
              refine ⟨15511376159147732956185719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10340917439431821970790479 15511376159147732956185719)
              ·
                refine ⟨23267064238721599434278579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15511376159147732956185719 23267064238721599434278579)
                ·
                  refine ⟨34900596358082399151417869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23267064238721599434278579 34900596358082399151417869)
                  ·
                    refine ⟨13087723634280899681781701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34900596358082399151417869 13087723634280899681781701)
                    ·
                      refine ⟨2453948181427668690334069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13087723634280899681781701 2453948181427668690334069)
                      ·
                        rfl

theorem cell23_4779047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_4779047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779047 prefixEnd_4779047 := by exact prefixLift 4779047
  have htrace : WordTrace (prefixWord ++ tailWord_4779047) baseStart_4779047 baseEnd_4779047 := by
    simpa [prefixWord, tailWord_4779047, baseEnd_4779047] using wordTrace_append hprefix tailTrace_4779047
  have hstable : (prefixWord ++ tailWord_4779047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779047).length < 2 ^ (prefixWord ++ tailWord_4779047).sum := by decide
  have hdescent : baseEnd_4779047 < baseStart_4779047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4779107 : List Nat := [1, 1, 1, 5, 1, 1, 1, 5, 2, 3, 2]
def baseStart_4779107 : Nat := 118140960795 + 4779107 * 2 ^ 59
def prefixEnd_4779107 : Nat := 4983230072969 + 3 ^ 40 * 4779107 * 2
def baseEnd_4779107 : Nat := 2453978990266938455583793

theorem tailTrace_4779107 : CollatzResearch.WordTrace tailWord_4779107 prefixEnd_4779107 2453978990266938455583793 := by
  unfold tailWord_4779107
  simp only [CollatzResearch.WordTrace]
  refine ⟨174308352297119020339191575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116205568198079346892794383 174308352297119020339191575)
  ·
    refine ⟨261462528445678530508787363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174308352297119020339191575 261462528445678530508787363)
    ·
      refine ⟨392193792668517795763181045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261462528445678530508787363 392193792668517795763181045)
      ·
        refine ⟨36768168062673543352798223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 392193792668517795763181045 36768168062673543352798223)
        ·
          refine ⟨55152252094010315029197335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36768168062673543352798223 55152252094010315029197335)
          ·
            refine ⟨82728378141015472543796003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55152252094010315029197335 82728378141015472543796003)
            ·
              refine ⟨124092567211523208815694005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82728378141015472543796003 124092567211523208815694005)
              ·
                refine ⟨11633678176080300826471313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 124092567211523208815694005 11633678176080300826471313)
                ·
                  refine ⟨8725258632060225619853485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11633678176080300826471313 8725258632060225619853485)
                  ·
                    refine ⟨3271971987022584607445057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8725258632060225619853485 3271971987022584607445057)
                    ·
                      refine ⟨2453978990266938455583793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3271971987022584607445057 2453978990266938455583793)
                      ·
                        rfl

theorem cell23_4779107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 2, 3, 2].length) (baseStart_4779107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779107 prefixEnd_4779107 := by exact prefixLift 4779107
  have htrace : WordTrace (prefixWord ++ tailWord_4779107) baseStart_4779107 baseEnd_4779107 := by
    simpa [prefixWord, tailWord_4779107, baseEnd_4779107] using wordTrace_append hprefix tailTrace_4779107
  have hstable : (prefixWord ++ tailWord_4779107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779107).length < 2 ^ (prefixWord ++ tailWord_4779107).sum := by decide
  have hdescent : baseEnd_4779107 < baseStart_4779107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4779117 : List Nat := [1, 5, 1, 1, 2, 2, 2, 3, 1, 5]
def baseStart_4779117 : Nat := 118140960795 + 4779117 * 2 ^ 59
def prefixEnd_4779117 : Nat := 4983230072969 + 3 ^ 40 * 4779117 * 2
def baseEnd_4779117 : Nat := 817994708357827805486249

theorem tailTrace_4779117 : CollatzResearch.WordTrace tailWord_4779117 prefixEnd_4779117 817994708357827805486249 := by
  unfold tailWord_4779117
  simp only [CollatzResearch.WordTrace]
  refine ⟨174308717027082792047055605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116205811351388528031370403 174308717027082792047055605)
  ·
    refine ⟨16341442221289011754411463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 174308717027082792047055605 16341442221289011754411463)
    ·
      refine ⟨24512163331933517631617195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16341442221289011754411463 24512163331933517631617195)
      ·
        refine ⟨36768244997900276447425793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24512163331933517631617195 36768244997900276447425793)
        ·
          refine ⟨27576183748425207335569345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36768244997900276447425793 27576183748425207335569345)
          ·
            refine ⟨20682137811318905501677009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27576183748425207335569345 20682137811318905501677009)
            ·
              refine ⟨15511603358489179126257757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20682137811318905501677009 15511603358489179126257757)
              ·
                refine ⟨5816851259433442172346659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15511603358489179126257757 5816851259433442172346659)
                ·
                  refine ⟨8725276889150163258519989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5816851259433442172346659 8725276889150163258519989)
                  ·
                    refine ⟨817994708357827805486249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8725276889150163258519989 817994708357827805486249)
                    ·
                      rfl

theorem cell23_4779117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_4779117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779117 prefixEnd_4779117 := by exact prefixLift 4779117
  have htrace : WordTrace (prefixWord ++ tailWord_4779117) baseStart_4779117 baseEnd_4779117 := by
    simpa [prefixWord, tailWord_4779117, baseEnd_4779117] using wordTrace_append hprefix tailTrace_4779117
  have hstable : (prefixWord ++ tailWord_4779117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779117).length < 2 ^ (prefixWord ++ tailWord_4779117).sum := by decide
  have hdescent : baseEnd_4779117 < baseStart_4779117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4779154 : List Nat := [3, 2, 3, 1, 1, 2, 3, 2, 1, 1, 4]
def baseStart_4779154 : Nat := 118140960795 + 4779154 * 2 ^ 59
def prefixEnd_4779154 : Nat := 4983230072969 + 3 ^ 40 * 4779154 * 2
def baseEnd_4779154 : Nat := 2454003123857699771696077

theorem tailTrace_4779154 : CollatzResearch.WordTrace tailWord_4779154 prefixEnd_4779154 2454003123857699771696077 := by
  unfold tailWord_4779154
  simp only [CollatzResearch.WordTrace]
  refine ⟨43577516631987186841538129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116206711018632498244101677 43577516631987186841538129)
  ·
    refine ⟨32683137473990390131153597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43577516631987186841538129 32683137473990390131153597)
    ·
      refine ⟨12256176552746396299182599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32683137473990390131153597 12256176552746396299182599)
      ·
        refine ⟨18384264829119594448773899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12256176552746396299182599 18384264829119594448773899)
        ·
          refine ⟨27576397243679391673160849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18384264829119594448773899 27576397243679391673160849)
          ·
            refine ⟨20682297932759543754870637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27576397243679391673160849 20682297932759543754870637)
            ·
              refine ⟨7755861724784828908076489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20682297932759543754870637 7755861724784828908076489)
              ·
                refine ⟨5816896293588621681057367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7755861724784828908076489 5816896293588621681057367)
                ·
                  refine ⟨8725344440382932521586051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5816896293588621681057367 8725344440382932521586051)
                  ·
                    refine ⟨13088016660574398782379077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8725344440382932521586051 13088016660574398782379077)
                    ·
                      refine ⟨2454003123857699771696077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13088016660574398782379077 2454003123857699771696077)
                      ·
                        rfl

theorem cell23_4779154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_4779154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779154 prefixEnd_4779154 := by exact prefixLift 4779154
  have htrace : WordTrace (prefixWord ++ tailWord_4779154) baseStart_4779154 baseEnd_4779154 := by
    simpa [prefixWord, tailWord_4779154, baseEnd_4779154] using wordTrace_append hprefix tailTrace_4779154
  have hstable : (prefixWord ++ tailWord_4779154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779154).length < 2 ^ (prefixWord ++ tailWord_4779154).sum := by decide
  have hdescent : baseEnd_4779154 < baseStart_4779154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4779157 : List Nat := [1, 3, 2, 1, 1, 1, 2, 6, 1, 2, 3]
def baseStart_4779157 : Nat := 118140960795 + 4779157 * 2 ^ 59
def prefixEnd_4779157 : Nat := 4983230072969 + 3 ^ 40 * 4779157 * 2
def baseEnd_4779157 : Nat := 2454004664299663259958563

theorem tailTrace_4779157 : CollatzResearch.WordTrace tailWord_4779157 prefixEnd_4779157 2454004664299663259958563 := by
  unfold tailWord_4779157
  simp only [CollatzResearch.WordTrace]
  refine ⟨174310175946937878878511725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116206783964625252585674483 174310175946937878878511725)
  ·
    refine ⟨65366315980101704579441897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174310175946937878878511725 65366315980101704579441897)
    ·
      refine ⟨49024736985076278434581423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65366315980101704579441897 49024736985076278434581423)
      ·
        refine ⟨73537105477614417651872135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49024736985076278434581423 73537105477614417651872135)
        ·
          refine ⟨110305658216421626477808203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73537105477614417651872135 110305658216421626477808203)
          ·
            refine ⟨165458487324632439716712305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110305658216421626477808203 165458487324632439716712305)
            ·
              refine ⟨124093865493474329787534229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165458487324632439716712305 124093865493474329787534229)
              ·
                refine ⟨5816899945006609208790667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 124093865493474329787534229 5816899945006609208790667)
                ·
                  refine ⟨8725349917509913813186001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5816899945006609208790667 8725349917509913813186001)
                  ·
                    refine ⟨6544012438132435359889501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8725349917509913813186001 6544012438132435359889501)
                    ·
                      refine ⟨2454004664299663259958563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6544012438132435359889501 2454004664299663259958563)
                      ·
                        rfl

theorem cell23_4779157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 6, 1, 2, 3].length) (baseStart_4779157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779157 prefixEnd_4779157 := by exact prefixLift 4779157
  have htrace : WordTrace (prefixWord ++ tailWord_4779157) baseStart_4779157 baseEnd_4779157 := by
    simpa [prefixWord, tailWord_4779157, baseEnd_4779157] using wordTrace_append hprefix tailTrace_4779157
  have hstable : (prefixWord ++ tailWord_4779157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779157).length < 2 ^ (prefixWord ++ tailWord_4779157).sum := by decide
  have hdescent : baseEnd_4779157 < baseStart_4779157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4779160 : List Nat := [2, 1, 2, 4, 2, 1, 2, 9]
def baseStart_4779160 : Nat := 118140960795 + 4779160 * 2 ^ 59
def prefixEnd_4779160 : Nat := 4983230072969 + 3 ^ 40 * 4779160 * 2
def baseEnd_4779160 : Nat := 90889118694134324008187

theorem tailTrace_4779160 : CollatzResearch.WordTrace tailWord_4779160 prefixEnd_4779160 90889118694134324008187 := by
  unfold tailWord_4779160
  simp only [CollatzResearch.WordTrace]
  refine ⟨87155142682963505195435467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116206856910618006927247289 87155142682963505195435467)
  ·
    refine ⟨130732714024445257793153201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87155142682963505195435467 130732714024445257793153201)
    ·
      refine ⟨98049535518333943344864901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130732714024445257793153201 98049535518333943344864901)
      ·
        refine ⟨18384287909687614377162169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98049535518333943344864901 18384287909687614377162169)
        ·
          refine ⟨13788215932265710782871627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18384287909687614377162169 13788215932265710782871627)
          ·
            refine ⟨20682323898398566174307441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13788215932265710782871627 20682323898398566174307441)
            ·
              refine ⟨15511742923798924630730581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20682323898398566174307441 15511742923798924630730581)
              ·
                refine ⟨90889118694134324008187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15511742923798924630730581 90889118694134324008187)
                ·
                  rfl

theorem cell23_4779160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 9].length) (baseStart_4779160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779160 prefixEnd_4779160 := by exact prefixLift 4779160
  have htrace : WordTrace (prefixWord ++ tailWord_4779160) baseStart_4779160 baseEnd_4779160 := by
    simpa [prefixWord, tailWord_4779160, baseEnd_4779160] using wordTrace_append hprefix tailTrace_4779160
  have hstable : (prefixWord ++ tailWord_4779160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779160).length < 2 ^ (prefixWord ++ tailWord_4779160).sum := by decide
  have hdescent : baseEnd_4779160 < baseStart_4779160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4779181 : List Nat := [1, 5, 2, 1, 3, 1, 2, 2, 2, 4]
def baseStart_4779181 : Nat := 118140960795 + 4779181 * 2 ^ 59
def prefixEnd_4779181 : Nat := 4983230072969 + 3 ^ 40 * 4779181 * 2
def baseEnd_4779181 : Nat := 818005662611790388686151

theorem tailTrace_4779181 : CollatzResearch.WordTrace tailWord_4779181 prefixEnd_4779181 818005662611790388686151 := by
  unfold tailWord_4779181
  simp only [CollatzResearch.WordTrace]
  refine ⟨174311051298850930977385397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116207367532567287318256931 174311051298850930977385397)
  ·
    refine ⟨16341661059267274779129881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 174311051298850930977385397 16341661059267274779129881)
    ·
      refine ⟨12256245794450456084347411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16341661059267274779129881 12256245794450456084347411)
      ·
        refine ⟨18384368691675684126521117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12256245794450456084347411 18384368691675684126521117)
        ·
          refine ⟨6894138259378381547445419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18384368691675684126521117 6894138259378381547445419)
          ·
            refine ⟨10341207389067572321168129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6894138259378381547445419 10341207389067572321168129)
            ·
              refine ⟨7755905541800679240876097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10341207389067572321168129 7755905541800679240876097)
              ·
                refine ⟨5816929156350509430657073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7755905541800679240876097 5816929156350509430657073)
                ·
                  refine ⟨4362696867262882072992805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5816929156350509430657073 4362696867262882072992805)
                  ·
                    refine ⟨818005662611790388686151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4362696867262882072992805 818005662611790388686151)
                    ·
                      rfl

theorem cell23_4779181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_4779181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779181 prefixEnd_4779181 := by exact prefixLift 4779181
  have htrace : WordTrace (prefixWord ++ tailWord_4779181) baseStart_4779181 baseEnd_4779181 := by
    simpa [prefixWord, tailWord_4779181, baseEnd_4779181] using wordTrace_append hprefix tailTrace_4779181
  have hstable : (prefixWord ++ tailWord_4779181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779181).length < 2 ^ (prefixWord ++ tailWord_4779181).sum := by decide
  have hdescent : baseEnd_4779181 < baseStart_4779181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4779187 : List Nat := [1, 1, 1, 2, 3, 2, 2, 3, 4, 1, 3]
def baseStart_4779187 : Nat := 118140960795 + 4779187 * 2 ^ 59
def prefixEnd_4779187 : Nat := 4983230072969 + 3 ^ 40 * 4779187 * 2
def baseEnd_4779187 : Nat := 2454020068719298142583425

theorem tailTrace_4779187 : CollatzResearch.WordTrace tailWord_4779187 prefixEnd_4779187 2454020068719298142583425 := by
  unfold tailWord_4779187
  simp only [CollatzResearch.WordTrace]
  refine ⟨174311270136829194002103815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116207513424552796001402543 174311270136829194002103815)
  ·
    refine ⟨261466905205243791003155723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174311270136829194002103815 261466905205243791003155723)
    ·
      refine ⟨392200357807865686504733585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261466905205243791003155723 392200357807865686504733585)
      ·
        refine ⟨294150268355899264878550189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 392200357807865686504733585 294150268355899264878550189)
        ·
          refine ⟨110306350633462224329456321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 294150268355899264878550189 110306350633462224329456321)
          ·
            refine ⟨82729762975096668247092241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110306350633462224329456321 82729762975096668247092241)
            ·
              refine ⟨62047322231322501185319181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82729762975096668247092241 62047322231322501185319181)
              ·
                refine ⟨23267745836745937944494693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62047322231322501185319181 23267745836745937944494693)
                ·
                  refine ⟨4362702344389863364592755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23267745836745937944494693 4362702344389863364592755)
                  ·
                    refine ⟨6544053516584795046889133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4362702344389863364592755 6544053516584795046889133)
                    ·
                      refine ⟨2454020068719298142583425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6544053516584795046889133 2454020068719298142583425)
                      ·
                        rfl

theorem cell23_4779187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 4, 1, 3].length) (baseStart_4779187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779187 prefixEnd_4779187 := by exact prefixLift 4779187
  have htrace : WordTrace (prefixWord ++ tailWord_4779187) baseStart_4779187 baseEnd_4779187 := by
    simpa [prefixWord, tailWord_4779187, baseEnd_4779187] using wordTrace_append hprefix tailTrace_4779187
  have hstable : (prefixWord ++ tailWord_4779187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779187).length < 2 ^ (prefixWord ++ tailWord_4779187).sum := by decide
  have hdescent : baseEnd_4779187 < baseStart_4779187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4779222 : List Nat := [5, 2, 1, 2, 2, 1, 2, 3, 1, 2, 2]
def baseStart_4779222 : Nat := 118140960795 + 4779222 * 2 ^ 59
def prefixEnd_4779222 : Nat := 4983230072969 + 3 ^ 40 * 4779222 * 2
def baseEnd_4779222 : Nat := 2454038040542205505645765

theorem tailTrace_4779222 : CollatzResearch.WordTrace tailWord_4779222 prefixEnd_4779222 2454038040542205505645765 := by
  unfold tailWord_4779222
  simp only [CollatzResearch.WordTrace]
  refine ⟨10894534168231399686226745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116208364461134929986418613 10894534168231399686226745)
  ·
    refine ⟨8170900626173549764670059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10894534168231399686226745 8170900626173549764670059)
    ·
      refine ⟨12256350939260324647005089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8170900626173549764670059 12256350939260324647005089)
      ·
        refine ⟨9192263204445243485253817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12256350939260324647005089 9192263204445243485253817)
        ·
          refine ⟨6894197403333932613940363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9192263204445243485253817 6894197403333932613940363)
          ·
            refine ⟨10341296105000898920910545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6894197403333932613940363 10341296105000898920910545)
            ·
              refine ⟨7755972078750674190682909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10341296105000898920910545 7755972078750674190682909)
              ·
                refine ⟨2908489529531502821506091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7755972078750674190682909 2908489529531502821506091)
                ·
                  refine ⟨4362734294297254232259137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2908489529531502821506091 4362734294297254232259137)
                  ·
                    refine ⟨3272050720722940674194353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4362734294297254232259137 3272050720722940674194353)
                    ·
                      refine ⟨2454038040542205505645765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3272050720722940674194353 2454038040542205505645765)
                      ·
                        rfl

theorem cell23_4779222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_4779222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779222 prefixEnd_4779222 := by exact prefixLift 4779222
  have htrace : WordTrace (prefixWord ++ tailWord_4779222) baseStart_4779222 baseEnd_4779222 := by
    simpa [prefixWord, tailWord_4779222, baseEnd_4779222] using wordTrace_append hprefix tailTrace_4779222
  have hstable : (prefixWord ++ tailWord_4779222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779222).length < 2 ^ (prefixWord ++ tailWord_4779222).sum := by decide
  have hdescent : baseEnd_4779222 < baseStart_4779222 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4779231 : List Nat := [1, 1, 2, 3, 2, 1, 6, 1, 1, 3, 2]
def baseStart_4779231 : Nat := 118140960795 + 4779231 * 2 ^ 59
def prefixEnd_4779231 : Nat := 4983230072969 + 3 ^ 40 * 4779231 * 2
def baseEnd_4779231 : Nat := 2454042661868095970433223

theorem tailTrace_4779231 : CollatzResearch.WordTrace tailWord_4779231 prefixEnd_4779231 2454042661868095970433223 := by
  unfold tailWord_4779231
  simp only [CollatzResearch.WordTrace]
  refine ⟨174312874948669789516705547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116208583299113193011137031 174312874948669789516705547)
  ·
    refine ⟨261469312423004684275058321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174312874948669789516705547 261469312423004684275058321)
    ·
      refine ⟨196101984317253513206293741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261469312423004684275058321 196101984317253513206293741)
      ·
        refine ⟨73538244118970067452360153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196101984317253513206293741 73538244118970067452360153)
        ·
          refine ⟨55153683089227550589270115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73538244118970067452360153 55153683089227550589270115)
          ·
            refine ⟨82730524633841325883905173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55153683089227550589270115 82730524633841325883905173)
            ·
              refine ⟨3877993342211312150808055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 82730524633841325883905173 3877993342211312150808055)
              ·
                refine ⟨5816990013316968226212083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3877993342211312150808055 5816990013316968226212083)
                ·
                  refine ⟨8725485019975452339318125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5816990013316968226212083 8725485019975452339318125)
                  ·
                    refine ⟨3272056882490794627244297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8725485019975452339318125 3272056882490794627244297)
                    ·
                      refine ⟨2454042661868095970433223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3272056882490794627244297 2454042661868095970433223)
                      ·
                        rfl

theorem cell23_4779231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 1, 1, 3, 2].length) (baseStart_4779231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779231 prefixEnd_4779231 := by exact prefixLift 4779231
  have htrace : WordTrace (prefixWord ++ tailWord_4779231) baseStart_4779231 baseEnd_4779231 := by
    simpa [prefixWord, tailWord_4779231, baseEnd_4779231] using wordTrace_append hprefix tailTrace_4779231
  have hstable : (prefixWord ++ tailWord_4779231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779231).length < 2 ^ (prefixWord ++ tailWord_4779231).sum := by decide
  have hdescent : baseEnd_4779231 < baseStart_4779231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
