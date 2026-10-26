import V185TrunkScan23Chunk1028

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6091624 : List Nat := [2, 1, 4, 2, 1, 2, 1, 1, 2, 3, 4]
def baseStart_6091624 : Nat := 118140960795 + 6091624 * 2 ^ 59
def prefixEnd_6091624 : Nat := 4983230072969 + 3 ^ 40 * 6091624 * 2
def baseEnd_6091624 : Nat := 3127931078464179726785137

theorem tailTrace_6091624 : CollatzResearch.WordTrace tailWord_6091624 prefixEnd_6091624 3127931078464179726785137 := by
  unfold tailWord_6091624
  simp only [CollatzResearch.WordTrace]
  refine ⟨111089890041547044698248963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148119853388729392930998617 111089890041547044698248963)
  ·
    refine ⟨166634835062320567047373445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111089890041547044698248963 166634835062320567047373445)
    ·
      refine ⟨31244031574185106321382521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166634835062320567047373445 31244031574185106321382521)
      ·
        refine ⟨23433023680638829741036891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31244031574185106321382521 23433023680638829741036891)
        ·
          refine ⟨35149535520958244611555337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23433023680638829741036891 35149535520958244611555337)
          ·
            refine ⟨26362151640718683458666503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35149535520958244611555337 26362151640718683458666503)
            ·
              refine ⟨39543227461078025187999755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26362151640718683458666503 39543227461078025187999755)
              ·
                refine ⟨59314841191617037781999633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39543227461078025187999755 59314841191617037781999633)
                ·
                  refine ⟨44486130893712778336499725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59314841191617037781999633 44486130893712778336499725)
                  ·
                    refine ⟨16682299085142291876187397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44486130893712778336499725 16682299085142291876187397)
                    ·
                      refine ⟨3127931078464179726785137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16682299085142291876187397 3127931078464179726785137)
                      ·
                        rfl

theorem cell23_6091624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_6091624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091624 prefixEnd_6091624 := by exact prefixLift 6091624
  have htrace : WordTrace (prefixWord ++ tailWord_6091624) baseStart_6091624 baseEnd_6091624 := by
    simpa [prefixWord, tailWord_6091624, baseEnd_6091624] using wordTrace_append hprefix tailTrace_6091624
  have hstable : (prefixWord ++ tailWord_6091624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091624).length < 2 ^ (prefixWord ++ tailWord_6091624).sum := by decide
  have hdescent : baseEnd_6091624 < baseStart_6091624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091627 : List Nat := [1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 5]
def baseStart_6091627 : Nat := 118140960795 + 6091627 * 2 ^ 59
def prefixEnd_6091627 : Nat := 4983230072969 + 3 ^ 40 * 6091627 * 2
def baseEnd_6091627 : Nat := 3127932618906143215047623

theorem tailTrace_6091627 : CollatzResearch.WordTrace tailWord_6091627 prefixEnd_6091627 3127932618906143215047623 := by
  unfold tailWord_6091627
  simp only [CollatzResearch.WordTrace]
  refine ⟨222179889502083220908857135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148119926334722147272571423 222179889502083220908857135)
  ·
    refine ⟨333269834253124831363285703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222179889502083220908857135 333269834253124831363285703)
    ·
      refine ⟨499904751379687247044928555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333269834253124831363285703 499904751379687247044928555)
      ·
        refine ⟨749857127069530870567392833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 499904751379687247044928555 749857127069530870567392833)
        ·
          refine ⟨562392845302148152925544625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 749857127069530870567392833 562392845302148152925544625)
          ·
            refine ⟨421794633976611114694158469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 562392845302148152925544625 421794633976611114694158469)
            ·
              refine ⟨79086493870614584005154713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 421794633976611114694158469 79086493870614584005154713)
              ·
                refine ⟨59314870402960938003866035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79086493870614584005154713 59314870402960938003866035)
                ·
                  refine ⟨88972305604441407005799053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59314870402960938003866035 88972305604441407005799053)
                  ·
                    refine ⟨33364614601665527627174645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88972305604441407005799053 33364614601665527627174645)
                    ·
                      refine ⟨3127932618906143215047623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33364614601665527627174645 3127932618906143215047623)
                      ·
                        rfl

theorem cell23_6091627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 5].length) (baseStart_6091627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091627 prefixEnd_6091627 := by exact prefixLift 6091627
  have htrace : WordTrace (prefixWord ++ tailWord_6091627) baseStart_6091627 baseEnd_6091627 := by
    simpa [prefixWord, tailWord_6091627, baseEnd_6091627] using wordTrace_append hprefix tailTrace_6091627
  have hstable : (prefixWord ++ tailWord_6091627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091627).length < 2 ^ (prefixWord ++ tailWord_6091627).sum := by decide
  have hdescent : baseEnd_6091627 < baseStart_6091627 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091641 : List Nat := [1, 2, 1, 3, 2, 3, 1, 3, 1, 4, 2]
def baseStart_6091641 : Nat := 118140960795 + 6091641 * 2 ^ 59
def prefixEnd_6091641 : Nat := 4983230072969 + 3 ^ 40 * 6091641 * 2
def baseEnd_6091641 : Nat := 3127939807635306160272559

theorem tailTrace_6091641 : CollatzResearch.WordTrace tailWord_6091641 prefixEnd_6091641 3127939807635306160272559 := by
  unfold tailWord_6091641
  simp only [CollatzResearch.WordTrace]
  refine ⟨222180400124032501299866777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148120266749355000866577851 222180400124032501299866777)
  ·
    refine ⟨166635300093024375974900083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222180400124032501299866777 166635300093024375974900083)
    ·
      refine ⟨249952950139536563962350125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166635300093024375974900083 249952950139536563962350125)
      ·
        refine ⟨93732356302326211485881297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249952950139536563962350125 93732356302326211485881297)
        ·
          refine ⟨70299267226744658614410973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93732356302326211485881297 70299267226744658614410973)
          ·
            refine ⟨26362225210029246980404115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70299267226744658614410973 26362225210029246980404115)
            ·
              refine ⟨39543337815043870470606173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26362225210029246980404115 39543337815043870470606173)
              ·
                refine ⟨14828751680641451426477315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39543337815043870470606173 14828751680641451426477315)
                ·
                  refine ⟨22243127520962177139715973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14828751680641451426477315 22243127520962177139715973)
                  ·
                    refine ⟨4170586410180408213696745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22243127520962177139715973 4170586410180408213696745)
                    ·
                      refine ⟨3127939807635306160272559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4170586410180408213696745 3127939807635306160272559)
                      ·
                        rfl

theorem cell23_6091641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 4, 2].length) (baseStart_6091641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091641 prefixEnd_6091641 := by exact prefixLift 6091641
  have htrace : WordTrace (prefixWord ++ tailWord_6091641) baseStart_6091641 baseEnd_6091641 := by
    simpa [prefixWord, tailWord_6091641, baseEnd_6091641] using wordTrace_append hprefix tailTrace_6091641
  have hstable : (prefixWord ++ tailWord_6091641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091641).length < 2 ^ (prefixWord ++ tailWord_6091641).sum := by decide
  have hdescent : baseEnd_6091641 < baseStart_6091641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091647 : List Nat := [1, 1, 2, 2, 1, 1, 5, 1, 9]
def baseStart_6091647 : Nat := 118140960795 + 6091647 * 2 ^ 59
def prefixEnd_6091647 : Nat := 4983230072969 + 3 ^ 40 * 6091647 * 2
def baseEnd_6091647 : Nat := 347549209835470348533059

theorem tailTrace_6091647 : CollatzResearch.WordTrace tailWord_6091647 prefixEnd_6091647 347549209835470348533059 := by
  unfold tailWord_6091647
  simp only [CollatzResearch.WordTrace]
  refine ⟨222180618962010764324585195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148120412641340509549723463 222180618962010764324585195)
  ·
    refine ⟨333270928443016146486877793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222180618962010764324585195 333270928443016146486877793)
    ·
      refine ⟨249953196332262109865158345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333270928443016146486877793 249953196332262109865158345)
      ·
        refine ⟨187464897249196582398868759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249953196332262109865158345 187464897249196582398868759)
        ·
          refine ⟨281197345873794873598303139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187464897249196582398868759 281197345873794873598303139)
          ·
            refine ⟨421796018810692310397454709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281197345873794873598303139 421796018810692310397454709)
            ·
              refine ⟨39543376763502404099761379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 421796018810692310397454709 39543376763502404099761379)
              ·
                refine ⟨59315065145253606149642069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39543376763502404099761379 59315065145253606149642069)
                ·
                  refine ⟨347549209835470348533059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59315065145253606149642069 347549209835470348533059)
                  ·
                    rfl

theorem cell23_6091647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 9].length) (baseStart_6091647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091647 prefixEnd_6091647 := by exact prefixLift 6091647
  have htrace : WordTrace (prefixWord ++ tailWord_6091647) baseStart_6091647 baseEnd_6091647 := by
    simpa [prefixWord, tailWord_6091647, baseEnd_6091647] using wordTrace_append hprefix tailTrace_6091647
  have hstable : (prefixWord ++ tailWord_6091647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091647).length < 2 ^ (prefixWord ++ tailWord_6091647).sum := by decide
  have hdescent : baseEnd_6091647 < baseStart_6091647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091658 : List Nat := [3, 1, 2, 4, 1, 1, 2, 2, 1, 4, 2]
def baseStart_6091658 : Nat := 118140960795 + 6091658 * 2 ^ 59
def prefixEnd_6091658 : Nat := 4983230072969 + 3 ^ 40 * 6091658 * 2
def baseEnd_6091658 : Nat := 3127948536806432593759981

theorem tailTrace_6091658 : CollatzResearch.WordTrace tailWord_6091658 prefixEnd_6091658 3127948536806432593759981 := by
  unfold tailWord_6091658
  simp only [CollatzResearch.WordTrace]
  refine ⟨55545255041242728300808907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148120680109980608802157085 55545255041242728300808907)
  ·
    refine ⟨83317882561864092451213361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55545255041242728300808907 83317882561864092451213361)
    ·
      refine ⟨62488411921398069338410021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83317882561864092451213361 62488411921398069338410021)
      ·
        refine ⟨11716577235262138000951879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62488411921398069338410021 11716577235262138000951879)
        ·
          refine ⟨17574865852893207001427819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11716577235262138000951879 17574865852893207001427819)
          ·
            refine ⟨26362298779339810502141729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17574865852893207001427819 26362298779339810502141729)
            ·
              refine ⟨19771724084504857876606297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26362298779339810502141729 19771724084504857876606297)
              ·
                refine ⟨14828793063378643407454723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19771724084504857876606297 14828793063378643407454723)
                ·
                  refine ⟨22243189595067965111182085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14828793063378643407454723 22243189595067965111182085)
                  ·
                    refine ⟨4170598049075243458346641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22243189595067965111182085 4170598049075243458346641)
                    ·
                      refine ⟨3127948536806432593759981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4170598049075243458346641 3127948536806432593759981)
                      ·
                        rfl

theorem cell23_6091658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_6091658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091658 prefixEnd_6091658 := by exact prefixLift 6091658
  have htrace : WordTrace (prefixWord ++ tailWord_6091658) baseStart_6091658 baseEnd_6091658 := by
    simpa [prefixWord, tailWord_6091658, baseEnd_6091658] using wordTrace_append hprefix tailTrace_6091658
  have hstable : (prefixWord ++ tailWord_6091658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091658).length < 2 ^ (prefixWord ++ tailWord_6091658).sum := by decide
  have hdescent : baseEnd_6091658 < baseStart_6091658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091681 : List Nat := [1, 2, 3, 4, 1, 2, 2, 1, 7]
def baseStart_6091681 : Nat := 118140960795 + 6091681 * 2 ^ 59
def prefixEnd_6091681 : Nat := 4983230072969 + 3 ^ 40 * 6091681 * 2
def baseEnd_6091681 : Nat := 347551149651276222641375

theorem tailTrace_6091681 : CollatzResearch.WordTrace tailWord_6091681 prefixEnd_6091681 347551149651276222641375 := by
  unfold tailWord_6091681
  simp only [CollatzResearch.WordTrace]
  refine ⟨222181859043887588131322897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148121239362591725420881931 222181859043887588131322897)
  ·
    refine ⟨166636394282915691098492173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222181859043887588131322897 166636394282915691098492173)
    ·
      refine ⟨62488647856093384161934565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166636394282915691098492173 62488647856093384161934565)
      ·
        refine ⟨11716621473017509530362731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62488647856093384161934565 11716621473017509530362731)
        ·
          refine ⟨17574932209526264295544097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11716621473017509530362731 17574932209526264295544097)
          ·
            refine ⟨13181199157144698221658073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17574932209526264295544097 13181199157144698221658073)
            ·
              refine ⟨9885899367858523666243555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13181199157144698221658073 9885899367858523666243555)
              ·
                refine ⟨14828849051787785499365333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9885899367858523666243555 14828849051787785499365333)
                ·
                  refine ⟨347551149651276222641375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14828849051787785499365333 347551149651276222641375)
                  ·
                    rfl

theorem cell23_6091681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 7].length) (baseStart_6091681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091681 prefixEnd_6091681 := by exact prefixLift 6091681
  have htrace : WordTrace (prefixWord ++ tailWord_6091681) baseStart_6091681 baseEnd_6091681 := by
    simpa [prefixWord, tailWord_6091681, baseEnd_6091681] using wordTrace_append hprefix tailTrace_6091681
  have hstable : (prefixWord ++ tailWord_6091681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091681).length < 2 ^ (prefixWord ++ tailWord_6091681).sum := by decide
  have hdescent : baseEnd_6091681 < baseStart_6091681 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091815 : List Nat := [1, 1, 7, 1, 1, 1, 1, 1, 5, 1, 3]
def baseStart_6091815 : Nat := 118140960795 + 6091815 * 2 ^ 59
def prefixEnd_6091815 : Nat := 4983230072969 + 3 ^ 40 * 6091815 * 2
def baseEnd_6091815 : Nat := 3128029153269188479496759

theorem tailTrace_6091815 : CollatzResearch.WordTrace tailWord_6091815 prefixEnd_6091815 3128029153269188479496759 := by
  unfold tailWord_6091815
  simp only [CollatzResearch.WordTrace]
  refine ⟨222186746425402129016700899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148124497616934752677800599 222186746425402129016700899)
  ·
    refine ⟨333280119638103193525051349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222186746425402129016700899 333280119638103193525051349)
    ·
      refine ⟨7811252804018043598243391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 333280119638103193525051349 7811252804018043598243391)
      ·
        refine ⟨11716879206027065397365087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7811252804018043598243391 11716879206027065397365087)
        ·
          refine ⟨17575318809040598096047631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11716879206027065397365087 17575318809040598096047631)
          ·
            refine ⟨26362978213560897144071447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17575318809040598096047631 26362978213560897144071447)
            ·
              refine ⟨39544467320341345716107171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26362978213560897144071447 39544467320341345716107171)
              ·
                refine ⟨59316700980512018574160757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39544467320341345716107171 59316700980512018574160757)
                ·
                  refine ⟨5560940716923001741327571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59316700980512018574160757 5560940716923001741327571)
                  ·
                    refine ⟨8341411075384502611991357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5560940716923001741327571 8341411075384502611991357)
                    ·
                      refine ⟨3128029153269188479496759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8341411075384502611991357 3128029153269188479496759)
                      ·
                        rfl

theorem cell23_6091815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_6091815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091815 prefixEnd_6091815 := by exact prefixLift 6091815
  have htrace : WordTrace (prefixWord ++ tailWord_6091815) baseStart_6091815 baseEnd_6091815 := by
    simpa [prefixWord, tailWord_6091815, baseEnd_6091815] using wordTrace_append hprefix tailTrace_6091815
  have hstable : (prefixWord ++ tailWord_6091815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091815).length < 2 ^ (prefixWord ++ tailWord_6091815).sum := by decide
  have hdescent : baseEnd_6091815 < baseStart_6091815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091831 : List Nat := [1, 1, 3, 1, 2, 2, 1, 4, 4, 4]
def baseStart_6091831 : Nat := 118140960795 + 6091831 * 2 ^ 59
def prefixEnd_6091831 : Nat := 4983230072969 + 3 ^ 40 * 6091831 * 2
def baseEnd_6091831 : Nat := 1042679122986553472298895

theorem tailTrace_6091831 : CollatzResearch.WordTrace tailWord_6091831 prefixEnd_6091831 1042679122986553472298895 := by
  unfold tailWord_6091831
  simp only [CollatzResearch.WordTrace]
  refine ⟨222187329993344163749283347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148124886662229442499522231 222187329993344163749283347)
  ·
    refine ⟨333280994990016245623925021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222187329993344163749283347 333280994990016245623925021)
    ·
      refine ⟨124980373121256092108971883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 333280994990016245623925021 124980373121256092108971883)
      ·
        refine ⟨187470559681884138163457825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124980373121256092108971883 187470559681884138163457825)
        ·
          refine ⟨140602919761413103622593369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187470559681884138163457825 140602919761413103622593369)
          ·
            refine ⟨105452189821059827716945027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140602919761413103622593369 105452189821059827716945027)
            ·
              refine ⟨158178284731589741575417541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105452189821059827716945027 158178284731589741575417541)
              ·
                refine ⟨29658428387173076545390789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 158178284731589741575417541 29658428387173076545390789)
                ·
                  refine ⟨5560955322594951852260773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29658428387173076545390789 5560955322594951852260773)
                  ·
                    refine ⟨1042679122986553472298895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5560955322594951852260773 1042679122986553472298895)
                    ·
                      rfl

theorem cell23_6091831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 4, 4].length) (baseStart_6091831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091831 prefixEnd_6091831 := by exact prefixLift 6091831
  have htrace : WordTrace (prefixWord ++ tailWord_6091831) baseStart_6091831 baseEnd_6091831 := by
    simpa [prefixWord, tailWord_6091831, baseEnd_6091831] using wordTrace_append hprefix tailTrace_6091831
  have hstable : (prefixWord ++ tailWord_6091831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091831).length < 2 ^ (prefixWord ++ tailWord_6091831).sum := by decide
  have hdescent : baseEnd_6091831 < baseStart_6091831 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091832 : List Nat := [2, 1, 2, 1, 5, 2, 2, 3, 1, 1, 3]
def baseStart_6091832 : Nat := 118140960795 + 6091832 * 2 ^ 59
def prefixEnd_6091832 : Nat := 4983230072969 + 3 ^ 40 * 6091832 * 2
def baseEnd_6091832 : Nat := 3128037882440314912984181

theorem tailTrace_6091832 : CollatzResearch.WordTrace tailWord_6091832 prefixEnd_6091832 3128037882440314912984181 := by
  unfold tailWord_6091832
  simp only [CollatzResearch.WordTrace]
  refine ⟨111093683233170270460034875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148124910977560360613379833 111093683233170270460034875)
  ·
    refine ⟨166640524849755405690052313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111093683233170270460034875 166640524849755405690052313)
    ·
      refine ⟨124980393637316554267539235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166640524849755405690052313 124980393637316554267539235)
      ·
        refine ⟨187470590455974831401308853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124980393637316554267539235 187470590455974831401308853)
        ·
          refine ⟨17575367855247640443872705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 187470590455974831401308853 17575367855247640443872705)
          ·
            refine ⟨13181525891435730332904529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17575367855247640443872705 13181525891435730332904529)
            ·
              refine ⟨9886144418576797749678397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13181525891435730332904529 9886144418576797749678397)
              ·
                refine ⟨3707304156966299156129399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9886144418576797749678397 3707304156966299156129399)
                ·
                  refine ⟨5560956235449448734194099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3707304156966299156129399 5560956235449448734194099)
                  ·
                    refine ⟨8341434353174173101291149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5560956235449448734194099 8341434353174173101291149)
                    ·
                      refine ⟨3128037882440314912984181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8341434353174173101291149 3128037882440314912984181)
                      ·
                        rfl

theorem cell23_6091832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 3, 1, 1, 3].length) (baseStart_6091832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091832 prefixEnd_6091832 := by exact prefixLift 6091832
  have htrace : WordTrace (prefixWord ++ tailWord_6091832) baseStart_6091832 baseEnd_6091832 := by
    simpa [prefixWord, tailWord_6091832, baseEnd_6091832] using wordTrace_append hprefix tailTrace_6091832
  have hstable : (prefixWord ++ tailWord_6091832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091832).length < 2 ^ (prefixWord ++ tailWord_6091832).sum := by decide
  have hdescent : baseEnd_6091832 < baseStart_6091832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091858 : List Nat := [3, 2, 2, 1, 3, 2, 1, 2, 1, 1, 5]
def baseStart_6091858 : Nat := 118140960795 + 6091858 * 2 ^ 59
def prefixEnd_6091858 : Nat := 4983230072969 + 3 ^ 40 * 6091858 * 2
def baseEnd_6091858 : Nat := 3128051232937331811259061

theorem tailTrace_6091858 : CollatzResearch.WordTrace tailWord_6091858 prefixEnd_6091858 3128051232937331811259061 := by
  unfold tailWord_6091858
  simp only [CollatzResearch.WordTrace]
  refine ⟨55547078691061586840129057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148125543176164231573677485 55547078691061586840129057)
  ·
    refine ⟨41660309018296190130096793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55547078691061586840129057 41660309018296190130096793)
    ·
      refine ⟨31245231763722142597572595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41660309018296190130096793 31245231763722142597572595)
      ·
        refine ⟨46867847645583213896358893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31245231763722142597572595 46867847645583213896358893)
        ·
          refine ⟨17575442867093705211134585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46867847645583213896358893 17575442867093705211134585)
          ·
            refine ⟨13181582150320278908350939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17575442867093705211134585 13181582150320278908350939)
            ·
              refine ⟨19772373225480418362526409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13181582150320278908350939 19772373225480418362526409)
              ·
                refine ⟨14829279919110313771894807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19772373225480418362526409 14829279919110313771894807)
                ·
                  refine ⟨22243919878665470657842211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14829279919110313771894807 22243919878665470657842211)
                  ·
                    refine ⟨33365879817998205986763317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22243919878665470657842211 33365879817998205986763317)
                    ·
                      refine ⟨3128051232937331811259061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33365879817998205986763317 3128051232937331811259061)
                      ·
                        rfl

theorem cell23_6091858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_6091858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091858 prefixEnd_6091858 := by exact prefixLift 6091858
  have htrace : WordTrace (prefixWord ++ tailWord_6091858) baseStart_6091858 baseEnd_6091858 := by
    simpa [prefixWord, tailWord_6091858, baseEnd_6091858] using wordTrace_append hprefix tailTrace_6091858
  have hstable : (prefixWord ++ tailWord_6091858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091858).length < 2 ^ (prefixWord ++ tailWord_6091858).sum := by decide
  have hdescent : baseEnd_6091858 < baseStart_6091858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091888 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 6, 1, 3]
def baseStart_6091888 : Nat := 118140960795 + 6091888 * 2 ^ 59
def prefixEnd_6091888 : Nat := 4983230072969 + 3 ^ 40 * 6091888 * 2
def baseEnd_6091888 : Nat := 3128066637356966693883923

theorem tailTrace_6091888 : CollatzResearch.WordTrace tailWord_6091888 prefixEnd_6091888 3128066637356966693883923 := by
  unfold tailWord_6091888
  simp only [CollatzResearch.WordTrace]
  refine ⟨111094704477068831242054159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148126272636091774989405545 111094704477068831242054159)
  ·
    refine ⟨166642056715603246863081239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111094704477068831242054159 166642056715603246863081239)
    ·
      refine ⟨249963085073404870294621859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166642056715603246863081239 249963085073404870294621859)
      ·
        refine ⟨374944627610107305441932789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249963085073404870294621859 374944627610107305441932789)
        ·
          refine ⟨35151058838447559885181199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 374944627610107305441932789 35151058838447559885181199)
          ·
            refine ⟨52726588257671339827771799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35151058838447559885181199 52726588257671339827771799)
            ·
              refine ⟨79089882386507009741657699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52726588257671339827771799 79089882386507009741657699)
              ·
                refine ⟨118634823579760514612486549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79089882386507009741657699 118634823579760514612486549)
                ·
                  refine ⟨5561007355301274122460307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 118634823579760514612486549 5561007355301274122460307)
                  ·
                    refine ⟨8341511032951911183690461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5561007355301274122460307 8341511032951911183690461)
                    ·
                      refine ⟨3128066637356966693883923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8341511032951911183690461 3128066637356966693883923)
                      ·
                        rfl

theorem cell23_6091888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 6, 1, 3].length) (baseStart_6091888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091888 prefixEnd_6091888 := by exact prefixLift 6091888
  have htrace : WordTrace (prefixWord ++ tailWord_6091888) baseStart_6091888 baseEnd_6091888 := by
    simpa [prefixWord, tailWord_6091888, baseEnd_6091888] using wordTrace_append hprefix tailTrace_6091888
  have hstable : (prefixWord ++ tailWord_6091888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091888).length < 2 ^ (prefixWord ++ tailWord_6091888).sum := by decide
  have hdescent : baseEnd_6091888 < baseStart_6091888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091901 : List Nat := [1, 4, 1, 1, 3, 1, 1, 2, 2, 2, 5]
def baseStart_6091901 : Nat := 118140960795 + 6091901 * 2 ^ 59
def prefixEnd_6091901 : Nat := 4983230072969 + 3 ^ 40 * 6091901 * 2
def baseEnd_6091901 : Nat := 3128073312605475143021363

theorem tailTrace_6091901 : CollatzResearch.WordTrace tailWord_6091901 prefixEnd_6091901 3128073312605475143021363 := by
  unfold tailWord_6091901
  simp only [CollatzResearch.WordTrace]
  refine ⟨222189883103090565704331557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148126588735393710469554371 222189883103090565704331557)
  ·
    refine ⟨41660603081829481069562167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222189883103090565704331557 41660603081829481069562167)
    ·
      refine ⟨62490904622744221604343251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41660603081829481069562167 62490904622744221604343251)
      ·
        refine ⟨93736356934116332406514877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62490904622744221604343251 93736356934116332406514877)
        ·
          refine ⟨35151133850293624652443079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93736356934116332406514877 35151133850293624652443079)
          ·
            refine ⟨52726700775440436978664619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35151133850293624652443079 52726700775440436978664619)
            ·
              refine ⟨79090051163160655467996929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52726700775440436978664619 79090051163160655467996929)
              ·
                refine ⟨59317538372370491600997697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79090051163160655467996929 59317538372370491600997697)
                ·
                  refine ⟨44488153779277868700748273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59317538372370491600997697 44488153779277868700748273)
                  ·
                    refine ⟨33366115334458401525561205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44488153779277868700748273 33366115334458401525561205)
                    ·
                      refine ⟨3128073312605475143021363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33366115334458401525561205 3128073312605475143021363)
                      ·
                        rfl

theorem cell23_6091901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_6091901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091901 prefixEnd_6091901 := by exact prefixLift 6091901
  have htrace : WordTrace (prefixWord ++ tailWord_6091901) baseStart_6091901 baseEnd_6091901 := by
    simpa [prefixWord, tailWord_6091901, baseEnd_6091901] using wordTrace_append hprefix tailTrace_6091901
  have hstable : (prefixWord ++ tailWord_6091901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091901).length < 2 ^ (prefixWord ++ tailWord_6091901).sum := by decide
  have hdescent : baseEnd_6091901 < baseStart_6091901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091905 : List Nat := [1, 2, 4, 2, 2, 1, 2, 1, 4, 1, 3]
def baseStart_6091905 : Nat := 118140960795 + 6091905 * 2 ^ 59
def prefixEnd_6091905 : Nat := 4983230072969 + 3 ^ 40 * 6091905 * 2
def baseEnd_6091905 : Nat := 3128075366528093127371345

theorem tailTrace_6091905 : CollatzResearch.WordTrace tailWord_6091905 prefixEnd_6091905 3128075366528093127371345 := by
  unfold tailWord_6091905
  simp only [CollatzResearch.WordTrace]
  refine ⟨222190028995076074387477169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148126685996717382924984779 222190028995076074387477169)
  ·
    refine ⟨166642521746307055790607877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222190028995076074387477169 166642521746307055790607877)
    ·
      refine ⟨31245472827432572960738977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166642521746307055790607877 31245472827432572960738977)
      ·
        refine ⟨23434104620574429720554233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31245472827432572960738977 23434104620574429720554233)
        ·
          refine ⟨17575578465430822290415675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23434104620574429720554233 17575578465430822290415675)
          ·
            refine ⟨26363367698146233435623513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17575578465430822290415675 26363367698146233435623513)
            ·
              refine ⟨19772525773609675076717635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26363367698146233435623513 19772525773609675076717635)
              ·
                refine ⟨29658788660414512615076453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19772525773609675076717635 29658788660414512615076453)
                ·
                  refine ⟨5561022873827721115326835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29658788660414512615076453 5561022873827721115326835)
                  ·
                    refine ⟨8341534310741581672990253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5561022873827721115326835 8341534310741581672990253)
                    ·
                      refine ⟨3128075366528093127371345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8341534310741581672990253 3128075366528093127371345)
                      ·
                        rfl

theorem cell23_6091905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_6091905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091905 prefixEnd_6091905 := by exact prefixLift 6091905
  have htrace : WordTrace (prefixWord ++ tailWord_6091905) baseStart_6091905 baseEnd_6091905 := by
    simpa [prefixWord, tailWord_6091905, baseEnd_6091905] using wordTrace_append hprefix tailTrace_6091905
  have hstable : (prefixWord ++ tailWord_6091905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091905).length < 2 ^ (prefixWord ++ tailWord_6091905).sum := by decide
  have hdescent : baseEnd_6091905 < baseStart_6091905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091911 : List Nat := [1, 1, 4, 2, 1, 1, 1, 3, 2, 3, 4]
def baseStart_6091911 : Nat := 118140960795 + 6091911 * 2 ^ 59
def prefixEnd_6091911 : Nat := 4983230072969 + 3 ^ 40 * 6091911 * 2
def baseEnd_6091911 : Nat := 3128078447412020103896317

theorem tailTrace_6091911 : CollatzResearch.WordTrace tailWord_6091911 prefixEnd_6091911 3128078447412020103896317 := by
  unfold tailWord_6091911
  simp only [CollatzResearch.WordTrace]
  refine ⟨222190247833054337412195587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148126831888702891608130391 222190247833054337412195587)
  ·
    refine ⟨333285371749581506118293381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222190247833054337412195587 333285371749581506118293381)
    ·
      refine ⟨62491007203046532397180009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 333285371749581506118293381 62491007203046532397180009)
      ·
        refine ⟨46868255402284899297885007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62491007203046532397180009 46868255402284899297885007)
        ·
          refine ⟨70302383103427348946827511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46868255402284899297885007 70302383103427348946827511)
          ·
            refine ⟨105453574655141023420241267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70302383103427348946827511 105453574655141023420241267)
            ·
              refine ⟨158180361982711535130361901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105453574655141023420241267 158180361982711535130361901)
              ·
                refine ⟨59317635743516825673885713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158180361982711535130361901 59317635743516825673885713)
                ·
                  refine ⟨44488226807637619255414285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59317635743516825673885713 44488226807637619255414285)
                  ·
                    refine ⟨16683085052864107220780357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44488226807637619255414285 16683085052864107220780357)
                    ·
                      refine ⟨3128078447412020103896317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16683085052864107220780357 3128078447412020103896317)
                      ·
                        rfl

theorem cell23_6091911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_6091911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091911 prefixEnd_6091911 := by exact prefixLift 6091911
  have htrace : WordTrace (prefixWord ++ tailWord_6091911) baseStart_6091911 baseEnd_6091911 := by
    simpa [prefixWord, tailWord_6091911, baseEnd_6091911] using wordTrace_append hprefix tailTrace_6091911
  have hstable : (prefixWord ++ tailWord_6091911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091911).length < 2 ^ (prefixWord ++ tailWord_6091911).sum := by decide
  have hdescent : baseEnd_6091911 < baseStart_6091911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091922 : List Nat := [3, 2, 3, 1, 1, 3, 1, 3, 2, 1, 3]
def baseStart_6091922 : Nat := 118140960795 + 6091922 * 2 ^ 59
def prefixEnd_6091922 : Nat := 4983230072969 + 3 ^ 40 * 6091922 * 2
def baseEnd_6091922 : Nat := 3128084095699219560858767

theorem tailTrace_6091922 : CollatzResearch.WordTrace tailWord_6091922 prefixEnd_6091922 3128084095699219560858767 := by
  unfold tailWord_6091922
  simp only [CollatzResearch.WordTrace]
  refine ⟨55547662259003621572711505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148127099357342990860564013 55547662259003621572711505)
  ·
    refine ⟨41660746694252716179533629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55547662259003621572711505 41660746694252716179533629)
    ·
      refine ⟨15622780010344768567325111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41660746694252716179533629 15622780010344768567325111)
      ·
        refine ⟨23434170015517152850987667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15622780010344768567325111 23434170015517152850987667)
        ·
          refine ⟨35151255023275729276481501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23434170015517152850987667 35151255023275729276481501)
          ·
            refine ⟨13181720633728398478680563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35151255023275729276481501 13181720633728398478680563)
            ·
              refine ⟨19772580950592597718020845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13181720633728398478680563 19772580950592597718020845)
              ·
                refine ⟨7414717856472224144257817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19772580950592597718020845 7414717856472224144257817)
                ·
                  refine ⟨5561038392354168108193363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7414717856472224144257817 5561038392354168108193363)
                  ·
                    refine ⟨8341557588531252162290045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5561038392354168108193363 8341557588531252162290045)
                    ·
                      refine ⟨3128084095699219560858767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8341557588531252162290045 3128084095699219560858767)
                      ·
                        rfl

theorem cell23_6091922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_6091922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091922 prefixEnd_6091922 := by exact prefixLift 6091922
  have htrace : WordTrace (prefixWord ++ tailWord_6091922) baseStart_6091922 baseEnd_6091922 := by
    simpa [prefixWord, tailWord_6091922, baseEnd_6091922] using wordTrace_append hprefix tailTrace_6091922
  have hstable : (prefixWord ++ tailWord_6091922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091922).length < 2 ^ (prefixWord ++ tailWord_6091922).sum := by decide
  have hdescent : baseEnd_6091922 < baseStart_6091922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091932 : List Nat := [2, 2, 3, 2, 1, 2, 3, 2, 1, 3, 2]
def baseStart_6091932 : Nat := 118140960795 + 6091932 * 2 ^ 59
def prefixEnd_6091932 : Nat := 4983230072969 + 3 ^ 40 * 6091932 * 2
def baseEnd_6091932 : Nat := 3128089230505764521733721

theorem tailTrace_6091932 : CollatzResearch.WordTrace tailWord_6091932 prefixEnd_6091932 3128089230505764521733721 := by
  unfold tailWord_6091932
  simp only [CollatzResearch.WordTrace]
  refine ⟨111095506882989128999355025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148127342510652171999140033 111095506882989128999355025)
  ·
    refine ⟨83321630162241846749516269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111095506882989128999355025 83321630162241846749516269)
    ·
      refine ⟨31245611310840692531068601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83321630162241846749516269 31245611310840692531068601)
      ·
        refine ⟨23434208483130519398301451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31245611310840692531068601 23434208483130519398301451)
        ·
          refine ⟨35151312724695779097452177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23434208483130519398301451 35151312724695779097452177)
          ·
            refine ⟨26363484543521834323089133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35151312724695779097452177 26363484543521834323089133)
            ·
              refine ⟨9886306703820687871158425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26363484543521834323089133 9886306703820687871158425)
              ·
                refine ⟨7414730027865515903368819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9886306703820687871158425 7414730027865515903368819)
                ·
                  refine ⟨11122095041798273855053229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7414730027865515903368819 11122095041798273855053229)
                  ·
                    refine ⟨4170785640674352695644961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11122095041798273855053229 4170785640674352695644961)
                    ·
                      refine ⟨3128089230505764521733721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4170785640674352695644961 3128089230505764521733721)
                      ·
                        rfl

theorem cell23_6091932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_6091932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091932 prefixEnd_6091932 := by exact prefixLift 6091932
  have htrace : WordTrace (prefixWord ++ tailWord_6091932) baseStart_6091932 baseEnd_6091932 := by
    simpa [prefixWord, tailWord_6091932, baseEnd_6091932] using wordTrace_append hprefix tailTrace_6091932
  have hstable : (prefixWord ++ tailWord_6091932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091932).length < 2 ^ (prefixWord ++ tailWord_6091932).sum := by decide
  have hdescent : baseEnd_6091932 < baseStart_6091932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091978 : List Nat := [3, 1, 2, 1, 3, 2, 1, 1, 1, 5, 3]
def baseStart_6091978 : Nat := 118140960795 + 6091978 * 2 ^ 59
def prefixEnd_6091978 : Nat := 4983230072969 + 3 ^ 40 * 6091978 * 2
def baseEnd_6091978 : Nat := 3128112850615871341758509

theorem tailTrace_6091978 : CollatzResearch.WordTrace tailWord_6091978 prefixEnd_6091978 3128112850615871341758509 := by
  unfold tailWord_6091978
  simp only [CollatzResearch.WordTrace]
  refine ⟨55548172880952901963721147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148128461015874405236589725 55548172880952901963721147)
  ·
    refine ⟨83322259321429352945581721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55548172880952901963721147 83322259321429352945581721)
    ·
      refine ⟨62491694491072014709186291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83322259321429352945581721 62491694491072014709186291)
      ·
        refine ⟨93737541736608022063779437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62491694491072014709186291 93737541736608022063779437)
        ·
          refine ⟨35151578151228008273917289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93737541736608022063779437 35151578151228008273917289)
          ·
            refine ⟨26363683613421006205437967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35151578151228008273917289 26363683613421006205437967)
            ·
              refine ⟨39545525420131509308156951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26363683613421006205437967 39545525420131509308156951)
              ·
                refine ⟨59318288130197263962235427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39545525420131509308156951 59318288130197263962235427)
                ·
                  refine ⟨88977432195295895943353141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59318288130197263962235427 88977432195295895943353141)
                  ·
                    refine ⟨8341634268308990244689357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 88977432195295895943353141 8341634268308990244689357)
                    ·
                      refine ⟨3128112850615871341758509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8341634268308990244689357 3128112850615871341758509)
                      ·
                        rfl

theorem cell23_6091978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 1, 5, 3].length) (baseStart_6091978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091978 prefixEnd_6091978 := by exact prefixLift 6091978
  have htrace : WordTrace (prefixWord ++ tailWord_6091978) baseStart_6091978 baseEnd_6091978 := by
    simpa [prefixWord, tailWord_6091978, baseEnd_6091978] using wordTrace_append hprefix tailTrace_6091978
  have hstable : (prefixWord ++ tailWord_6091978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091978).length < 2 ^ (prefixWord ++ tailWord_6091978).sum := by decide
  have hdescent : baseEnd_6091978 < baseStart_6091978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091991 : List Nat := [1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 7]
def baseStart_6091991 : Nat := 118140960795 + 6091991 * 2 ^ 59
def prefixEnd_6091991 : Nat := 4983230072969 + 3 ^ 40 * 6091991 * 2
def baseEnd_6091991 : Nat := 3128119525864379790895949

theorem tailTrace_6091991 : CollatzResearch.WordTrace tailWord_6091991 prefixEnd_6091991 3128119525864379790895949 := by
  unfold tailWord_6091991
  simp only [CollatzResearch.WordTrace]
  refine ⟨222193165672764511075107827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148128777115176340716738551 222193165672764511075107827)
  ·
    refine ⟨333289748509146766612661741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222193165672764511075107827 333289748509146766612661741)
    ·
      refine ⟨124983655690930037479748153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 333289748509146766612661741 124983655690930037479748153)
      ·
        refine ⟨93737741768197528109811115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124983655690930037479748153 93737741768197528109811115)
        ·
          refine ⟨140606612652296292164716673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93737741768197528109811115 140606612652296292164716673)
          ·
            refine ⟨105454959489222219123537505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140606612652296292164716673 105454959489222219123537505)
            ·
              refine ⟨79091219616916664342653129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105454959489222219123537505 79091219616916664342653129)
              ·
                refine ⟨59318414712687498256989847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79091219616916664342653129 59318414712687498256989847)
                ·
                  refine ⟨88977622069031247385484771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59318414712687498256989847 88977622069031247385484771)
                  ·
                    refine ⟨133466433103546871078227157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 88977622069031247385484771 133466433103546871078227157)
                    ·
                      refine ⟨3128119525864379790895949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 133466433103546871078227157 3128119525864379790895949)
                      ·
                        rfl

theorem cell23_6091991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_6091991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091991 prefixEnd_6091991 := by exact prefixLift 6091991
  have htrace : WordTrace (prefixWord ++ tailWord_6091991) baseStart_6091991 baseEnd_6091991 := by
    simpa [prefixWord, tailWord_6091991, baseEnd_6091991] using wordTrace_append hprefix tailTrace_6091991
  have hstable : (prefixWord ++ tailWord_6091991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091991).length < 2 ^ (prefixWord ++ tailWord_6091991).sum := by decide
  have hdescent : baseEnd_6091991 < baseStart_6091991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092035 : List Nat := [1, 1, 1, 3, 2, 4, 2, 1, 2, 4, 2]
def baseStart_6092035 : Nat := 118140960795 + 6092035 * 2 ^ 59
def prefixEnd_6092035 : Nat := 4983230072969 + 3 ^ 40 * 6092035 * 2
def baseEnd_6092035 : Nat := 3128142119013177618745747

theorem tailTrace_6092035 : CollatzResearch.WordTrace tailWord_6092035 prefixEnd_6092035 3128142119013177618745747 := by
  unfold tailWord_6092035
  simp only [CollatzResearch.WordTrace]
  refine ⟨222194770484605106589709559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148129846989736737726473039 222194770484605106589709559)
  ·
    refine ⟨333292155726907659884564339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222194770484605106589709559 333292155726907659884564339)
    ·
      refine ⟨499938233590361489826846509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333292155726907659884564339 499938233590361489826846509)
      ·
        refine ⟨187476837596385558685067441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 499938233590361489826846509 187476837596385558685067441)
        ·
          refine ⟨140607628197289169013800581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187476837596385558685067441 140607628197289169013800581)
          ·
            refine ⟨26363930286991719190087609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140607628197289169013800581 26363930286991719190087609)
            ·
              refine ⟨19772947715243789392565707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26363930286991719190087609 19772947715243789392565707)
              ·
                refine ⟨29659421572865684088848561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19772947715243789392565707 29659421572865684088848561)
                ·
                  refine ⟨22244566179649263066636421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29659421572865684088848561 22244566179649263066636421)
                  ·
                    refine ⟨4170856158684236824994329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22244566179649263066636421 4170856158684236824994329)
                    ·
                      refine ⟨3128142119013177618745747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4170856158684236824994329 3128142119013177618745747)
                      ·
                        rfl

theorem cell23_6092035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 4, 2].length) (baseStart_6092035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092035 prefixEnd_6092035 := by exact prefixLift 6092035
  have htrace : WordTrace (prefixWord ++ tailWord_6092035) baseStart_6092035 baseEnd_6092035 := by
    simpa [prefixWord, tailWord_6092035, baseEnd_6092035] using wordTrace_append hprefix tailTrace_6092035
  have hstable : (prefixWord ++ tailWord_6092035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092035).length < 2 ^ (prefixWord ++ tailWord_6092035).sum := by decide
  have hdescent : baseEnd_6092035 < baseStart_6092035 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092051 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 9]
def baseStart_6092051 : Nat := 118140960795 + 6092051 * 2 ^ 59
def prefixEnd_6092051 : Nat := 4983230072969 + 3 ^ 40 * 6092051 * 2
def baseEnd_6092051 : Nat := 3128150334703649556145673

theorem tailTrace_6092051 : CollatzResearch.WordTrace tailWord_6092051 prefixEnd_6092051 3128150334703649556145673 := by
  unfold tailWord_6092051
  simp only [CollatzResearch.WordTrace]
  refine ⟨222195354052547141322292007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148130236035031427548194671 222195354052547141322292007)
  ·
    refine ⟨333293031078820711983438011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222195354052547141322292007 333293031078820711983438011)
    ·
      refine ⟨499939546618231067975157017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333293031078820711983438011 499939546618231067975157017)
      ·
        refine ⟨374954659963673300981367763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 499939546618231067975157017 374954659963673300981367763)
        ·
          refine ⟨562431989945509951472051645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374954659963673300981367763 562431989945509951472051645)
          ·
            refine ⟨210911996229566231802019367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 562431989945509951472051645 210911996229566231802019367)
            ·
              refine ⟨316367994344349347703029051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210911996229566231802019367 316367994344349347703029051)
              ·
                refine ⟨474551991516524021554543577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 316367994344349347703029051 474551991516524021554543577)
                ·
                  refine ⟨355913993637393016165907683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 474551991516524021554543577 355913993637393016165907683)
                  ·
                    refine ⟨533870990456089524248861525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 355913993637393016165907683 533870990456089524248861525)
                    ·
                      refine ⟨3128150334703649556145673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 533870990456089524248861525 3128150334703649556145673)
                      ·
                        rfl

theorem cell23_6092051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 9].length) (baseStart_6092051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092051 prefixEnd_6092051 := by exact prefixLift 6092051
  have htrace : WordTrace (prefixWord ++ tailWord_6092051) baseStart_6092051 baseEnd_6092051 := by
    simpa [prefixWord, tailWord_6092051, baseEnd_6092051] using wordTrace_append hprefix tailTrace_6092051
  have hstable : (prefixWord ++ tailWord_6092051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092051).length < 2 ^ (prefixWord ++ tailWord_6092051).sum := by decide
  have hdescent : baseEnd_6092051 < baseStart_6092051 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092055 : List Nat := [1, 1, 3, 4, 1, 1, 2, 3, 2, 2, 3]
def baseStart_6092055 : Nat := 118140960795 + 6092055 * 2 ^ 59
def prefixEnd_6092055 : Nat := 4983230072969 + 3 ^ 40 * 6092055 * 2
def baseEnd_6092055 : Nat := 3128152388626267540495655

theorem tailTrace_6092055 : CollatzResearch.WordTrace tailWord_6092055 prefixEnd_6092055 3128152388626267540495655 := by
  unfold tailWord_6092055
  simp only [CollatzResearch.WordTrace]
  refine ⟨222195499944532650005437619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148130333296355100003625079 222195499944532650005437619)
  ·
    refine ⟨333293249916798975008156429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222195499944532650005437619 333293249916798975008156429)
    ·
      refine ⟨124984968718799615628058661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 333293249916798975008156429 124984968718799615628058661)
      ·
        refine ⟨23434681634774927930260999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124984968718799615628058661 23434681634774927930260999)
        ·
          refine ⟨35152022452162391895391499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23434681634774927930260999 35152022452162391895391499)
          ·
            refine ⟨52728033678243587843087249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35152022452162391895391499 52728033678243587843087249)
            ·
              refine ⟨39546025258682690882315437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52728033678243587843087249 39546025258682690882315437)
              ·
                refine ⟨14829759472006009080868289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39546025258682690882315437 14829759472006009080868289)
                ·
                  refine ⟨11122319604004506810651217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14829759472006009080868289 11122319604004506810651217)
                  ·
                    refine ⟨8341739703003380107988413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11122319604004506810651217 8341739703003380107988413)
                    ·
                      refine ⟨3128152388626267540495655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8341739703003380107988413 3128152388626267540495655)
                      ·
                        rfl

theorem cell23_6092055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_6092055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092055 prefixEnd_6092055 := by exact prefixLift 6092055
  have htrace : WordTrace (prefixWord ++ tailWord_6092055) baseStart_6092055 baseEnd_6092055 := by
    simpa [prefixWord, tailWord_6092055, baseEnd_6092055] using wordTrace_append hprefix tailTrace_6092055
  have hstable : (prefixWord ++ tailWord_6092055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092055).length < 2 ^ (prefixWord ++ tailWord_6092055).sum := by decide
  have hdescent : baseEnd_6092055 < baseStart_6092055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092058 : List Nat := [3, 1, 1, 3, 3, 1, 1, 2, 8]
def baseStart_6092058 : Nat := 118140960795 + 6092058 * 2 ^ 59
def prefixEnd_6092058 : Nat := 4983230072969 + 3 ^ 40 * 6092058 * 2
def baseEnd_6092058 : Nat := 347572658785359003195349

theorem tailTrace_6092058 : CollatzResearch.WordTrace tailWord_6092058 prefixEnd_6092058 347572658785359003195349 := by
  unfold tailWord_6092058
  simp only [CollatzResearch.WordTrace]
  refine ⟨55548902340880445379449207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148130406242347854345197885 55548902340880445379449207)
  ·
    refine ⟨83323353511320668069173811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55548902340880445379449207 83323353511320668069173811)
    ·
      refine ⟨124985030266981002103760717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83323353511320668069173811 124985030266981002103760717)
      ·
        refine ⟨46869386350117875788910269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124985030266981002103760717 46869386350117875788910269)
        ·
          refine ⟨17576019881294203420841351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46869386350117875788910269 17576019881294203420841351)
          ·
            refine ⟨26364029821941305131262027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17576019881294203420841351 26364029821941305131262027)
            ·
              refine ⟨39546044732911957696893041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26364029821941305131262027 39546044732911957696893041)
              ·
                refine ⟨29659533549683968272669781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39546044732911957696893041 29659533549683968272669781)
                ·
                  refine ⟨347572658785359003195349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29659533549683968272669781 347572658785359003195349)
                  ·
                    rfl

theorem cell23_6092058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 8].length) (baseStart_6092058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092058 prefixEnd_6092058 := by exact prefixLift 6092058
  have htrace : WordTrace (prefixWord ++ tailWord_6092058) baseStart_6092058 baseEnd_6092058 := by
    simpa [prefixWord, tailWord_6092058, baseEnd_6092058] using wordTrace_append hprefix tailTrace_6092058
  have hstable : (prefixWord ++ tailWord_6092058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092058).length < 2 ^ (prefixWord ++ tailWord_6092058).sum := by decide
  have hdescent : baseEnd_6092058 < baseStart_6092058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092072 : List Nat := [2, 1, 5, 1, 2, 2, 1, 2, 2, 2, 3]
def baseStart_6092072 : Nat := 118140960795 + 6092072 * 2 ^ 59
def prefixEnd_6092072 : Nat := 4983230072969 + 3 ^ 40 * 6092072 * 2
def baseEnd_6092072 : Nat := 3128161117797393973983077

theorem tailTrace_6092072 : CollatzResearch.WordTrace tailWord_6092072 prefixEnd_6092072 3128161117797393973983077 := by
  unfold tailWord_6092072
  simp only [CollatzResearch.WordTrace]
  refine ⟨111098059992735530954403235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148130746656980707939204313 111098059992735530954403235)
  ·
    refine ⟨166647089989103296431604853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111098059992735530954403235 166647089989103296431604853)
    ·
      refine ⟨15623164686478434040462955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 166647089989103296431604853 15623164686478434040462955)
      ·
        refine ⟨23434747029717651060694433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15623164686478434040462955 23434747029717651060694433)
        ·
          refine ⟨17576060272288238295520825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23434747029717651060694433 17576060272288238295520825)
          ·
            refine ⟨13182045204216178721640619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17576060272288238295520825 13182045204216178721640619)
            ·
              refine ⟨19773067806324268082460929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13182045204216178721640619 19773067806324268082460929)
              ·
                refine ⟨14829800854743201061845697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19773067806324268082460929 14829800854743201061845697)
                ·
                  refine ⟨11122350641057400796384273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14829800854743201061845697 11122350641057400796384273)
                  ·
                    refine ⟨8341762980793050597288205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11122350641057400796384273 8341762980793050597288205)
                    ·
                      refine ⟨3128161117797393973983077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8341762980793050597288205 3128161117797393973983077)
                      ·
                        rfl

theorem cell23_6092072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_6092072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092072 prefixEnd_6092072 := by exact prefixLift 6092072
  have htrace : WordTrace (prefixWord ++ tailWord_6092072) baseStart_6092072 baseEnd_6092072 := by
    simpa [prefixWord, tailWord_6092072, baseEnd_6092072] using wordTrace_append hprefix tailTrace_6092072
  have hstable : (prefixWord ++ tailWord_6092072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092072).length < 2 ^ (prefixWord ++ tailWord_6092072).sum := by decide
  have hdescent : baseEnd_6092072 < baseStart_6092072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092088 : List Nat := [2, 1, 2, 1, 3, 1, 1, 4, 3, 5]
def baseStart_6092088 : Nat := 118140960795 + 6092088 * 2 ^ 59
def prefixEnd_6092088 : Nat := 4983230072969 + 3 ^ 40 * 6092088 * 2
def baseEnd_6092088 : Nat := 1042723111162621970461001

theorem tailTrace_6092088 : CollatzResearch.WordTrace tailWord_6092088 prefixEnd_6092088 1042723111162621970461001 := by
  unfold tailWord_6092088
  simp only [CollatzResearch.WordTrace]
  refine ⟨111098351776706548320694459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148131135702275397760925945 111098351776706548320694459)
  ·
    refine ⟨166647527665059822481041689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111098351776706548320694459 166647527665059822481041689)
    ·
      refine ⟨124985645748794866860781267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166647527665059822481041689 124985645748794866860781267)
      ·
        refine ⟨187478468623192300291171901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124985645748794866860781267 187478468623192300291171901)
        ·
          refine ⟨70304425733697112609189463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187478468623192300291171901 70304425733697112609189463)
          ·
            refine ⟨105456638600545668913784195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70304425733697112609189463 105456638600545668913784195)
            ·
              refine ⟨158184957900818503370676293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105456638600545668913784195 158184957900818503370676293)
              ·
                refine ⟨29659679606403469382001805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 158184957900818503370676293 29659679606403469382001805)
                ·
                  refine ⟨11122379852401301018250677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29659679606403469382001805 11122379852401301018250677)
                  ·
                    refine ⟨1042723111162621970461001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11122379852401301018250677 1042723111162621970461001)
                    ·
                      rfl

theorem cell23_6092088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 3, 5].length) (baseStart_6092088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092088 prefixEnd_6092088 := by exact prefixLift 6092088
  have htrace : WordTrace (prefixWord ++ tailWord_6092088) baseStart_6092088 baseEnd_6092088 := by
    simpa [prefixWord, tailWord_6092088, baseEnd_6092088] using wordTrace_append hprefix tailTrace_6092088
  have hstable : (prefixWord ++ tailWord_6092088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092088).length < 2 ^ (prefixWord ++ tailWord_6092088).sum := by decide
  have hdescent : baseEnd_6092088 < baseStart_6092088 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092092 : List Nat := [2, 2, 2, 2, 1, 5, 2, 1, 6]
def baseStart_6092092 : Nat := 118140960795 + 6092092 * 2 ^ 59
def prefixEnd_6092092 : Nat := 4983230072969 + 3 ^ 40 * 6092092 * 2
def baseEnd_6092092 : Nat := 347574598601164877303665

theorem tailTrace_6092092 : CollatzResearch.WordTrace tailWord_6092092 prefixEnd_6092092 347574598601164877303665 := by
  unfold tailWord_6092092
  simp only [CollatzResearch.WordTrace]
  refine ⟨111098424722699302662267265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148131232963599070216356353 111098424722699302662267265)
  ·
    refine ⟨83323818542024476996700449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111098424722699302662267265 83323818542024476996700449)
    ·
      refine ⟨62492863906518357747525337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83323818542024476996700449 62492863906518357747525337)
      ·
        refine ⟨46869647929888768310644003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62492863906518357747525337 46869647929888768310644003)
        ·
          refine ⟨70304471894833152465966005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46869647929888768310644003 70304471894833152465966005)
          ·
            refine ⟨6591044240140608043684313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70304471894833152465966005 6591044240140608043684313)
            ·
              refine ⟨4943283180105456032763235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6591044240140608043684313 4943283180105456032763235)
              ·
                refine ⟨7414924770158184049144853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4943283180105456032763235 7414924770158184049144853)
                ·
                  refine ⟨347574598601164877303665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7414924770158184049144853 347574598601164877303665)
                  ·
                    rfl

theorem cell23_6092092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 1, 6].length) (baseStart_6092092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092092 prefixEnd_6092092 := by exact prefixLift 6092092
  have htrace : WordTrace (prefixWord ++ tailWord_6092092) baseStart_6092092 baseEnd_6092092 := by
    simpa [prefixWord, tailWord_6092092, baseEnd_6092092] using wordTrace_append hprefix tailTrace_6092092
  have hstable : (prefixWord ++ tailWord_6092092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092092).length < 2 ^ (prefixWord ++ tailWord_6092092).sum := by decide
  have hdescent : baseEnd_6092092 < baseStart_6092092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092105 : List Nat := [1, 2, 1, 1, 2, 3, 5, 2, 1, 5]
def baseStart_6092105 : Nat := 118140960795 + 6092105 * 2 ^ 59
def prefixEnd_6092105 : Nat := 4983230072969 + 3 ^ 40 * 6092105 * 2
def baseEnd_6092105 : Nat := 1042726020886330781623475

theorem tailTrace_6092105 : CollatzResearch.WordTrace tailWord_6092105 prefixEnd_6092105 1042726020886330781623475 := by
  unfold tailWord_6092105
  simp only [CollatzResearch.WordTrace]
  refine ⟨222197323594351508544757769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148131549062901005696505179 222197323594351508544757769)
  ·
    refine ⟨166647992695763631408568327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222197323594351508544757769 166647992695763631408568327)
    ·
      refine ⟨249971989043645447112852491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166647992695763631408568327 249971989043645447112852491)
      ·
        refine ⟨374957983565468170669278737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249971989043645447112852491 374957983565468170669278737)
        ·
          refine ⟨281218487674101128001959053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374957983565468170669278737 281218487674101128001959053)
          ·
            refine ⟨105456932877787923000734645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 281218487674101128001959053 105456932877787923000734645)
            ·
              refine ⟨9886587457292617781318873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 105456932877787923000734645 9886587457292617781318873)
              ·
                refine ⟨7414940592969463335989155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9886587457292617781318873 7414940592969463335989155)
                ·
                  refine ⟨11122410889454195003983733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7414940592969463335989155 11122410889454195003983733)
                  ·
                    refine ⟨1042726020886330781623475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11122410889454195003983733 1042726020886330781623475)
                    ·
                      rfl

theorem cell23_6092105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 2, 1, 5].length) (baseStart_6092105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092105 prefixEnd_6092105 := by exact prefixLift 6092105
  have htrace : WordTrace (prefixWord ++ tailWord_6092105) baseStart_6092105 baseEnd_6092105 := by
    simpa [prefixWord, tailWord_6092105, baseEnd_6092105] using wordTrace_append hprefix tailTrace_6092105
  have hstable : (prefixWord ++ tailWord_6092105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092105).length < 2 ^ (prefixWord ++ tailWord_6092105).sum := by decide
  have hdescent : baseEnd_6092105 < baseStart_6092105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092112 : List Nat := [2, 1, 1, 1, 1, 5, 4, 1, 2, 3, 2]
def baseStart_6092112 : Nat := 118140960795 + 6092112 * 2 ^ 59
def prefixEnd_6092112 : Nat := 4983230072969 + 3 ^ 40 * 6092112 * 2
def baseEnd_6092112 : Nat := 3128181657023573817482893

theorem tailTrace_6092112 : CollatzResearch.WordTrace tailWord_6092112 prefixEnd_6092112 3128181657023573817482893 := by
  unfold tailWord_6092112
  simp only [CollatzResearch.WordTrace]
  refine ⟨111098789452663074370131295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148131719270217432493508393 111098789452663074370131295)
  ·
    refine ⟨166648184178994611555196943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111098789452663074370131295 166648184178994611555196943)
    ·
      refine ⟨249972276268491917332795415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166648184178994611555196943 249972276268491917332795415)
      ·
        refine ⟨374958414402737875999193123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249972276268491917332795415 374958414402737875999193123)
        ·
          refine ⟨562437621604106813998789685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374958414402737875999193123 562437621604106813998789685)
          ·
            refine ⟨52728527025385013812386533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 562437621604106813998789685 52728527025385013812386533)
            ·
              refine ⟨9886598817259690089822475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52728527025385013812386533 9886598817259690089822475)
              ·
                refine ⟨14829898225889535134733713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9886598817259690089822475 14829898225889535134733713)
                ·
                  refine ⟨11122423669417151351050285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14829898225889535134733713 11122423669417151351050285)
                  ·
                    refine ⟨4170908876031431756643857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11122423669417151351050285 4170908876031431756643857)
                    ·
                      refine ⟨3128181657023573817482893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4170908876031431756643857 3128181657023573817482893)
                      ·
                        rfl

theorem cell23_6092112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 2, 3, 2].length) (baseStart_6092112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092112 prefixEnd_6092112 := by exact prefixLift 6092112
  have htrace : WordTrace (prefixWord ++ tailWord_6092112) baseStart_6092112 baseEnd_6092112 := by
    simpa [prefixWord, tailWord_6092112, baseEnd_6092112] using wordTrace_append hprefix tailTrace_6092112
  have hstable : (prefixWord ++ tailWord_6092112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092112).length < 2 ^ (prefixWord ++ tailWord_6092112).sum := by decide
  have hdescent : baseEnd_6092112 < baseStart_6092112 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092136 : List Nat := [2, 1, 4, 2, 3, 1, 1, 4, 1, 1, 3]
def baseStart_6092136 : Nat := 118140960795 + 6092136 * 2 ^ 59
def prefixEnd_6092136 : Nat := 4983230072969 + 3 ^ 40 * 6092136 * 2
def baseEnd_6092136 : Nat := 3128193980559281723582783

theorem tailTrace_6092136 : CollatzResearch.WordTrace tailWord_6092136 prefixEnd_6092136 3128193980559281723582783 := by
  unfold tailWord_6092136
  simp only [CollatzResearch.WordTrace]
  refine ⟨111099227128619600419568131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148132302838159467226090841 111099227128619600419568131)
  ·
    refine ⟨166648840692929400629352197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111099227128619600419568131 166648840692929400629352197)
    ·
      refine ⟨31246657629924262618003537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166648840692929400629352197 31246657629924262618003537)
      ·
        refine ⟨23434993222443196963502653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31246657629924262618003537 23434993222443196963502653)
        ·
          refine ⟨8788122458416198861313495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23434993222443196963502653 8788122458416198861313495)
          ·
            refine ⟨13182183687624298291970243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8788122458416198861313495 13182183687624298291970243)
            ·
              refine ⟨19773275531436447437955365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13182183687624298291970243 19773275531436447437955365)
              ·
                refine ⟨3707489162144333894616631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19773275531436447437955365 3707489162144333894616631)
                ·
                  refine ⟨5561233743216500841924947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3707489162144333894616631 5561233743216500841924947)
                  ·
                    refine ⟨8341850614824751262887421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5561233743216500841924947 8341850614824751262887421)
                    ·
                      refine ⟨3128193980559281723582783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8341850614824751262887421 3128193980559281723582783)
                      ·
                        rfl

theorem cell23_6092136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_6092136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092136 prefixEnd_6092136 := by exact prefixLift 6092136
  have htrace : WordTrace (prefixWord ++ tailWord_6092136) baseStart_6092136 baseEnd_6092136 := by
    simpa [prefixWord, tailWord_6092136, baseEnd_6092136] using wordTrace_append hprefix tailTrace_6092136
  have hstable : (prefixWord ++ tailWord_6092136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092136).length < 2 ^ (prefixWord ++ tailWord_6092136).sum := by decide
  have hdescent : baseEnd_6092136 < baseStart_6092136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092145 : List Nat := [1, 2, 2, 2, 1, 2, 3, 2, 3, 2, 3]
def baseStart_6092145 : Nat := 118140960795 + 6092145 * 2 ^ 59
def prefixEnd_6092145 : Nat := 4983230072969 + 3 ^ 40 * 6092145 * 2
def baseEnd_6092145 : Nat := 3128198601885172188370241

theorem tailTrace_6092145 : CollatzResearch.WordTrace tailWord_6092145 prefixEnd_6092145 3128198601885172188370241 := by
  unfold tailWord_6092145
  simp only [CollatzResearch.WordTrace]
  refine ⟨222198782514206595376213889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148132521676137730250809259 222198782514206595376213889)
  ·
    refine ⟨166649086885654946532160417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222198782514206595376213889 166649086885654946532160417)
    ·
      refine ⟨124986815164241209899120313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166649086885654946532160417 124986815164241209899120313)
      ·
        refine ⟨93740111373180907424340235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124986815164241209899120313 93740111373180907424340235)
        ·
          refine ⟨140610167059771361136510353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93740111373180907424340235 140610167059771361136510353)
          ·
            refine ⟨105457625294828520852382765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140610167059771361136510353 105457625294828520852382765)
            ·
              refine ⟨39546609485560695319643537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105457625294828520852382765 39546609485560695319643537)
              ·
                refine ⟨29659957114170521489732653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39546609485560695319643537 29659957114170521489732653)
                ·
                  refine ⟨11122483917813945558649745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29659957114170521489732653 11122483917813945558649745)
                  ·
                    refine ⟨8341862938360459168987309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11122483917813945558649745 8341862938360459168987309)
                    ·
                      refine ⟨3128198601885172188370241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8341862938360459168987309 3128198601885172188370241)
                      ·
                        rfl

theorem cell23_6092145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 3, 2, 3].length) (baseStart_6092145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092145 prefixEnd_6092145 := by exact prefixLift 6092145
  have htrace : WordTrace (prefixWord ++ tailWord_6092145) baseStart_6092145 baseEnd_6092145 := by
    simpa [prefixWord, tailWord_6092145, baseEnd_6092145] using wordTrace_append hprefix tailTrace_6092145
  have hstable : (prefixWord ++ tailWord_6092145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092145).length < 2 ^ (prefixWord ++ tailWord_6092145).sum := by decide
  have hdescent : baseEnd_6092145 < baseStart_6092145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092155 : List Nat := [1, 1, 1, 1, 1, 6, 4, 1, 1, 2, 4]
def baseStart_6092155 : Nat := 118140960795 + 6092155 * 2 ^ 59
def prefixEnd_6092155 : Nat := 4983230072969 + 3 ^ 40 * 6092155 * 2
def baseEnd_6092155 : Nat := 3128203736691717149245195

theorem tailTrace_6092155 : CollatzResearch.WordTrace tailWord_6092155 prefixEnd_6092155 3128203736691717149245195 := by
  unfold tailWord_6092155
  simp only [CollatzResearch.WordTrace]
  refine ⟨222199147244170367084077919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148132764829446911389385279 222199147244170367084077919)
  ·
    refine ⟨333298720866255550626116879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222199147244170367084077919 333298720866255550626116879)
    ·
      refine ⟨499948081299383325939175319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333298720866255550626116879 499948081299383325939175319)
      ·
        refine ⟨749922121949074988908762979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 499948081299383325939175319 749922121949074988908762979)
        ·
          refine ⟨1124883182923612483363144469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 749922121949074988908762979 1124883182923612483363144469)
          ·
            refine ⟨52728899199544335157647397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1124883182923612483363144469 52728899199544335157647397)
            ·
              refine ⟨9886668599914562842058887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52728899199544335157647397 9886668599914562842058887)
              ·
                refine ⟨14830002899871844263088331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9886668599914562842058887 14830002899871844263088331)
                ·
                  refine ⟨22245004349807766394632497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14830002899871844263088331 22245004349807766394632497)
                  ·
                    refine ⟨16683753262355824795974373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22245004349807766394632497 16683753262355824795974373)
                    ·
                      refine ⟨3128203736691717149245195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16683753262355824795974373 3128203736691717149245195)
                      ·
                        rfl

theorem cell23_6092155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 2, 4].length) (baseStart_6092155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092155 prefixEnd_6092155 := by exact prefixLift 6092155
  have htrace : WordTrace (prefixWord ++ tailWord_6092155) baseStart_6092155 baseEnd_6092155 := by
    simpa [prefixWord, tailWord_6092155, baseEnd_6092155] using wordTrace_append hprefix tailTrace_6092155
  have hstable : (prefixWord ++ tailWord_6092155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092155).length < 2 ^ (prefixWord ++ tailWord_6092155).sum := by decide
  have hdescent : baseEnd_6092155 < baseStart_6092155 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092192 : List Nat := [2, 1, 1, 4, 1, 2, 3, 1, 4, 1, 3]
def baseStart_6092192 : Nat := 118140960795 + 6092192 * 2 ^ 59
def prefixEnd_6092192 : Nat := 4983230072969 + 3 ^ 40 * 6092192 * 2
def baseEnd_6092192 : Nat := 3128222735475933504482525

theorem tailTrace_6092192 : CollatzResearch.WordTrace tailWord_6092192 prefixEnd_6092192 3128222735475933504482525 := by
  unfold tailWord_6092192
  simp only [CollatzResearch.WordTrace]
  refine ⟨111100248372518161201587415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148133664496690881602116553 111100248372518161201587415)
  ·
    refine ⟨166650372558777241802381123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111100248372518161201587415 166650372558777241802381123)
    ·
      refine ⟨249975558838165862703571685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166650372558777241802381123 249975558838165862703571685)
      ·
        refine ⟨46870417282156099256919691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 249975558838165862703571685 46870417282156099256919691)
        ·
          refine ⟨70305625923234148885379537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46870417282156099256919691 70305625923234148885379537)
          ·
            refine ⟨52729219442425611664034653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70305625923234148885379537 52729219442425611664034653)
            ·
              refine ⟨19773457290909604374012995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52729219442425611664034653 19773457290909604374012995)
              ·
                refine ⟨29660185936364406561019493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19773457290909604374012995 29660185936364406561019493)
                ·
                  refine ⟨5561284863068326230191155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29660185936364406561019493 5561284863068326230191155)
                  ·
                    refine ⟨8341927294602489345286733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5561284863068326230191155 8341927294602489345286733)
                    ·
                      refine ⟨3128222735475933504482525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8341927294602489345286733 3128222735475933504482525)
                      ·
                        rfl

theorem cell23_6092192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_6092192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092192 prefixEnd_6092192 := by exact prefixLift 6092192
  have htrace : WordTrace (prefixWord ++ tailWord_6092192) baseStart_6092192 baseEnd_6092192 := by
    simpa [prefixWord, tailWord_6092192, baseEnd_6092192] using wordTrace_append hprefix tailTrace_6092192
  have hstable : (prefixWord ++ tailWord_6092192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092192).length < 2 ^ (prefixWord ++ tailWord_6092192).sum := by decide
  have hdescent : baseEnd_6092192 < baseStart_6092192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092208 : List Nat := [2, 1, 1, 1, 2, 1, 1, 5, 1, 8]
def baseStart_6092208 : Nat := 118140960795 + 6092208 * 2 ^ 59
def prefixEnd_6092208 : Nat := 4983230072969 + 3 ^ 40 * 6092208 * 2
def baseEnd_6092208 : Nat := 1042743650388801813960817

theorem tailTrace_6092208 : CollatzResearch.WordTrace tailWord_6092208 prefixEnd_6092208 1042743650388801813960817 := by
  unfold tailWord_6092208
  simp only [CollatzResearch.WordTrace]
  refine ⟨111100540156489178567878639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148134053541985571423838185 111100540156489178567878639)
  ·
    refine ⟨166650810234733767851817959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111100540156489178567878639 166650810234733767851817959)
    ·
      refine ⟨249976215352100651777726939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166650810234733767851817959 249976215352100651777726939)
      ·
        refine ⟨374964323028150977666590409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249976215352100651777726939 374964323028150977666590409)
        ·
          refine ⟨281223242271113233249942807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374964323028150977666590409 281223242271113233249942807)
          ·
            refine ⟨421834863406669849874914211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281223242271113233249942807 421834863406669849874914211)
            ·
              refine ⟨632752295110004774812371317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 421834863406669849874914211 632752295110004774812371317)
              ·
                refine ⟨59320527666562947638659811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 632752295110004774812371317 59320527666562947638659811)
                ·
                  refine ⟨88980791499844421457989717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59320527666562947638659811 88980791499844421457989717)
                  ·
                    refine ⟨1042743650388801813960817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 88980791499844421457989717 1042743650388801813960817)
                    ·
                      rfl

theorem cell23_6092208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 1, 8].length) (baseStart_6092208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092208 prefixEnd_6092208 := by exact prefixLift 6092208
  have htrace : WordTrace (prefixWord ++ tailWord_6092208) baseStart_6092208 baseEnd_6092208 := by
    simpa [prefixWord, tailWord_6092208, baseEnd_6092208] using wordTrace_append hprefix tailTrace_6092208
  have hstable : (prefixWord ++ tailWord_6092208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092208).length < 2 ^ (prefixWord ++ tailWord_6092208).sum := by decide
  have hdescent : baseEnd_6092208 < baseStart_6092208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092232 : List Nat := [2, 1, 3, 1, 3, 1, 2, 1, 3, 4, 2]
def baseStart_6092232 : Nat := 118140960795 + 6092232 * 2 ^ 59
def prefixEnd_6092232 : Nat := 4983230072969 + 3 ^ 40 * 6092232 * 2
def baseEnd_6092232 : Nat := 3128243274702113347982341

theorem tailTrace_6092232 : CollatzResearch.WordTrace tailWord_6092232 prefixEnd_6092232 3128243274702113347982341 := by
  unfold tailWord_6092232
  simp only [CollatzResearch.WordTrace]
  refine ⟨111100977832445704617315475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148134637109927606156420633 111100977832445704617315475)
  ·
    refine ⟨166651466748668556925973213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111100977832445704617315475 166651466748668556925973213)
    ·
      refine ⟨62494300030750708847239955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166651466748668556925973213 62494300030750708847239955)
      ·
        refine ⟨93741450046126063270859933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62494300030750708847239955 93741450046126063270859933)
        ·
          refine ⟨35153043767297273726572475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93741450046126063270859933 35153043767297273726572475)
          ·
            refine ⟨52729565650945910589858713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35153043767297273726572475 52729565650945910589858713)
            ·
              refine ⟨39547174238209432942394035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52729565650945910589858713 39547174238209432942394035)
              ·
                refine ⟨59320761357314149413591053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39547174238209432942394035 59320761357314149413591053)
                ·
                  refine ⟨22245285508992806030096645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59320761357314149413591053 22245285508992806030096645)
                  ·
                    refine ⟨4170991032936151130643121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22245285508992806030096645 4170991032936151130643121)
                    ·
                      refine ⟨3128243274702113347982341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4170991032936151130643121 3128243274702113347982341)
                      ·
                        rfl

theorem cell23_6092232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 3, 4, 2].length) (baseStart_6092232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092232 prefixEnd_6092232 := by exact prefixLift 6092232
  have htrace : WordTrace (prefixWord ++ tailWord_6092232) baseStart_6092232 baseEnd_6092232 := by
    simpa [prefixWord, tailWord_6092232, baseEnd_6092232] using wordTrace_append hprefix tailTrace_6092232
  have hstable : (prefixWord ++ tailWord_6092232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092232).length < 2 ^ (prefixWord ++ tailWord_6092232).sum := by decide
  have hdescent : baseEnd_6092232 < baseStart_6092232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092249 : List Nat := [1, 2, 1, 2, 4, 2, 2, 1, 4, 2, 2]
def baseStart_6092249 : Nat := 118140960795 + 6092249 * 2 ^ 59
def prefixEnd_6092249 : Nat := 4983230072969 + 3 ^ 40 * 6092249 * 2
def baseEnd_6092249 : Nat := 3128252003873239781469763

theorem tailTrace_6092249 : CollatzResearch.WordTrace tailWord_6092249 prefixEnd_6092249 3128252003873239781469763 := by
  unfold tailWord_6092249
  simp only [CollatzResearch.WordTrace]
  refine ⟨222202575705829821137999801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148135050470553214091999867 222202575705829821137999801)
  ·
    refine ⟨166651931779372365853499851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222202575705829821137999801 166651931779372365853499851)
    ·
      refine ⟨249977897669058548780249777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166651931779372365853499851 249977897669058548780249777)
      ·
        refine ⟨187483423251793911585187333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249977897669058548780249777 187483423251793911585187333)
        ·
          refine ⟨35153141859711358422222625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 187483423251793911585187333 35153141859711358422222625)
          ·
            refine ⟨26364856394783518816666969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35153141859711358422222625 26364856394783518816666969)
            ·
              refine ⟨19773642296087639112500227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26364856394783518816666969 19773642296087639112500227)
              ·
                refine ⟨29660463444131458668750341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19773642296087639112500227 29660463444131458668750341)
                ·
                  refine ⟨5561336895774648500390689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29660463444131458668750341 5561336895774648500390689)
                  ·
                    refine ⟨4171002671830986375293017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5561336895774648500390689 4171002671830986375293017)
                    ·
                      refine ⟨3128252003873239781469763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4171002671830986375293017 3128252003873239781469763)
                      ·
                        rfl

theorem cell23_6092249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 4, 2, 2].length) (baseStart_6092249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092249 prefixEnd_6092249 := by exact prefixLift 6092249
  have htrace : WordTrace (prefixWord ++ tailWord_6092249) baseStart_6092249 baseEnd_6092249 := by
    simpa [prefixWord, tailWord_6092249, baseEnd_6092249] using wordTrace_append hprefix tailTrace_6092249
  have hstable : (prefixWord ++ tailWord_6092249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092249).length < 2 ^ (prefixWord ++ tailWord_6092249).sum := by decide
  have hdescent : baseEnd_6092249 < baseStart_6092249 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092265 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 6, 3, 3]
def baseStart_6092265 : Nat := 118140960795 + 6092265 * 2 ^ 59
def prefixEnd_6092265 : Nat := 4983230072969 + 3 ^ 40 * 6092265 * 2
def baseEnd_6092265 : Nat := 3128260219563711718869689

theorem tailTrace_6092265 : CollatzResearch.WordTrace tailWord_6092265 prefixEnd_6092265 3128260219563711718869689 := by
  unfold tailWord_6092265
  simp only [CollatzResearch.WordTrace]
  refine ⟨222203159273771855870582249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148135439515847903913721499 222203159273771855870582249)
  ·
    refine ⟨166652369455328891902936687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222203159273771855870582249 166652369455328891902936687)
    ·
      refine ⟨249978554182993337854405031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166652369455328891902936687 249978554182993337854405031)
      ·
        refine ⟨374967831274490006781607547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249978554182993337854405031 374967831274490006781607547)
        ·
          refine ⟨562451746911735010172411321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374967831274490006781607547 562451746911735010172411321)
          ·
            refine ⟨421838810183801257629308491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 562451746911735010172411321 421838810183801257629308491)
            ·
              refine ⟨632758215275701886443962737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 421838810183801257629308491 632758215275701886443962737)
              ·
                refine ⟨474568661456776414832972053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 632758215275701886443962737 474568661456776414832972053)
                ·
                  refine ⟨22245406005786394445295565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 474568661456776414832972053 22245406005786394445295565)
                  ·
                    refine ⟨8342027252169897916985837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22245406005786394445295565 8342027252169897916985837)
                    ·
                      refine ⟨3128260219563711718869689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8342027252169897916985837 3128260219563711718869689)
                      ·
                        rfl

theorem cell23_6092265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 3, 3].length) (baseStart_6092265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092265 prefixEnd_6092265 := by exact prefixLift 6092265
  have htrace : WordTrace (prefixWord ++ tailWord_6092265) baseStart_6092265 baseEnd_6092265 := by
    simpa [prefixWord, tailWord_6092265, baseEnd_6092265] using wordTrace_append hprefix tailTrace_6092265
  have hstable : (prefixWord ++ tailWord_6092265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092265).length < 2 ^ (prefixWord ++ tailWord_6092265).sum := by decide
  have hdescent : baseEnd_6092265 < baseStart_6092265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092322 : List Nat := [3, 3, 1, 1, 1, 1, 2, 2, 4, 1, 4]
def baseStart_6092322 : Nat := 118140960795 + 6092322 * 2 ^ 59
def prefixEnd_6092322 : Nat := 4983230072969 + 3 ^ 40 * 6092322 * 2
def baseEnd_6092322 : Nat := 3128289487961017995856927

theorem tailTrace_6092322 : CollatzResearch.WordTrace tailWord_6092322 prefixEnd_6092322 3128289487961017995856927 := by
  unfold tailWord_6092322
  simp only [CollatzResearch.WordTrace]
  refine ⟨55551309558641338651351805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148136825489710236403604813 55551309558641338651351805)
  ·
    refine ⟨20831741084490501994256927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55551309558641338651351805 20831741084490501994256927)
    ·
      refine ⟨31247611626735752991385391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20831741084490501994256927 31247611626735752991385391)
      ·
        refine ⟨46871417440103629487078087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31247611626735752991385391 46871417440103629487078087)
        ·
          refine ⟨70307126160155444230617131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46871417440103629487078087 70307126160155444230617131)
          ·
            refine ⟨105460689240233166345925697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70307126160155444230617131 105460689240233166345925697)
            ·
              refine ⟨79095516930174874759444273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105460689240233166345925697 79095516930174874759444273)
              ·
                refine ⟨59321637697631156069583205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79095516930174874759444273 59321637697631156069583205)
                ·
                  refine ⟨11122807068305841763046851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59321637697631156069583205 11122807068305841763046851)
                  ·
                    refine ⟨16684210602458762644570277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11122807068305841763046851 16684210602458762644570277)
                    ·
                      refine ⟨3128289487961017995856927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16684210602458762644570277 3128289487961017995856927)
                      ·
                        rfl

theorem cell23_6092322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_6092322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092322 prefixEnd_6092322 := by exact prefixLift 6092322
  have htrace : WordTrace (prefixWord ++ tailWord_6092322) baseStart_6092322 baseEnd_6092322 := by
    simpa [prefixWord, tailWord_6092322, baseEnd_6092322] using wordTrace_append hprefix tailTrace_6092322
  have hstable : (prefixWord ++ tailWord_6092322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092322).length < 2 ^ (prefixWord ++ tailWord_6092322).sum := by decide
  have hdescent : baseEnd_6092322 < baseStart_6092322 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092339 : List Nat := [1, 1, 1, 2, 4, 5, 1, 1, 2, 1, 4]
def baseStart_6092339 : Nat := 118140960795 + 6092339 * 2 ^ 59
def prefixEnd_6092339 : Nat := 4983230072969 + 3 ^ 40 * 6092339 * 2
def baseEnd_6092339 : Nat := 3128298217132144429344349

theorem tailTrace_6092339 : CollatzResearch.WordTrace tailWord_6092339 prefixEnd_6092339 3128298217132144429344349 := by
  unfold tailWord_6092339
  simp only [CollatzResearch.WordTrace]
  refine ⟨222205858275503766508776071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148137238850335844339184047 222205858275503766508776071)
  ·
    refine ⟨333308787413255649763164107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222205858275503766508776071 333308787413255649763164107)
    ·
      refine ⟨499963181119883474644746161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333308787413255649763164107 499963181119883474644746161)
      ·
        refine ⟨374972385839912605983559621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 499963181119883474644746161 374972385839912605983559621)
        ·
          refine ⟨70307322344983613621917429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 374972385839912605983559621 70307322344983613621917429)
          ·
            refine ⟨6591311469842213777054759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70307322344983613621917429 6591311469842213777054759)
            ·
              refine ⟨9886967204763320665582139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6591311469842213777054759 9886967204763320665582139)
              ·
                refine ⟨14830450807144980998373209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9886967204763320665582139 14830450807144980998373209)
                ·
                  refine ⟨11122838105358735748779907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14830450807144980998373209 11122838105358735748779907)
                  ·
                    refine ⟨16684257158038103623169861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11122838105358735748779907 16684257158038103623169861)
                    ·
                      refine ⟨3128298217132144429344349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16684257158038103623169861 3128298217132144429344349)
                      ·
                        rfl

theorem cell23_6092339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 2, 1, 4].length) (baseStart_6092339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092339 prefixEnd_6092339 := by exact prefixLift 6092339
  have htrace : WordTrace (prefixWord ++ tailWord_6092339) baseStart_6092339 baseEnd_6092339 := by
    simpa [prefixWord, tailWord_6092339, baseEnd_6092339] using wordTrace_append hprefix tailTrace_6092339
  have hstable : (prefixWord ++ tailWord_6092339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092339).length < 2 ^ (prefixWord ++ tailWord_6092339).sum := by decide
  have hdescent : baseEnd_6092339 < baseStart_6092339 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092399 : List Nat := [1, 1, 2, 1, 3, 2, 1, 5, 2, 3, 2]
def baseStart_6092399 : Nat := 118140960795 + 6092399 * 2 ^ 59
def prefixEnd_6092399 : Nat := 4983230072969 + 3 ^ 40 * 6092399 * 2
def baseEnd_6092399 : Nat := 3128329025971414194594073

theorem tailTrace_6092399 : CollatzResearch.WordTrace tailWord_6092399 prefixEnd_6092399 3128329025971414194594073 := by
  unfold tailWord_6092399
  simp only [CollatzResearch.WordTrace]
  refine ⟨222208046655286396755960251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148138697770190931170640167 222208046655286396755960251)
  ·
    refine ⟨333312069982929595133940377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222208046655286396755960251 333312069982929595133940377)
    ·
      refine ⟨249984052487197196350455283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333312069982929595133940377 249984052487197196350455283)
      ·
        refine ⟨374976078730795794525682925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249984052487197196350455283 374976078730795794525682925)
        ·
          refine ⟨140616029524048422947131097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 374976078730795794525682925 140616029524048422947131097)
          ·
            refine ⟨105462022143036317210348323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140616029524048422947131097 105462022143036317210348323)
            ·
              refine ⟨158193033214554475815522485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105462022143036317210348323 158193033214554475815522485)
              ·
                refine ⟨14830596863864482107705233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 158193033214554475815522485 14830596863864482107705233)
                ·
                  refine ⟨11122947647898361580778925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14830596863864482107705233 11122947647898361580778925)
                  ·
                    refine ⟨4171105367961885592792097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11122947647898361580778925 4171105367961885592792097)
                    ·
                      refine ⟨3128329025971414194594073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4171105367961885592792097 3128329025971414194594073)
                      ·
                        rfl

theorem cell23_6092399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 2, 3, 2].length) (baseStart_6092399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092399 prefixEnd_6092399 := by exact prefixLift 6092399
  have htrace : WordTrace (prefixWord ++ tailWord_6092399) baseStart_6092399 baseEnd_6092399 := by
    simpa [prefixWord, tailWord_6092399, baseEnd_6092399] using wordTrace_append hprefix tailTrace_6092399
  have hstable : (prefixWord ++ tailWord_6092399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092399).length < 2 ^ (prefixWord ++ tailWord_6092399).sum := by decide
  have hdescent : baseEnd_6092399 < baseStart_6092399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092412 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 5, 1, 4]
def baseStart_6092412 : Nat := 118140960795 + 6092412 * 2 ^ 59
def prefixEnd_6092412 : Nat := 4983230072969 + 3 ^ 40 * 6092412 * 2
def baseEnd_6092412 : Nat := 3128335701219922643731513

theorem tailTrace_6092412 : CollatzResearch.WordTrace tailWord_6092412 prefixEnd_6092412 3128335701219922643731513 := by
  unfold tailWord_6092412
  simp only [CollatzResearch.WordTrace]
  refine ⟨111104260402119649988091745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148139013869492866650788993 111104260402119649988091745)
  ·
    refine ⟨83328195301589737491068809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111104260402119649988091745 83328195301589737491068809)
    ·
      refine ⟨62496146476192303118301607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83328195301589737491068809 62496146476192303118301607)
      ·
        refine ⟨93744219714288454677452411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62496146476192303118301607 93744219714288454677452411)
        ·
          refine ⟨140616329571432682016178617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93744219714288454677452411 140616329571432682016178617)
          ·
            refine ⟨105462247178574511512133963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140616329571432682016178617 105462247178574511512133963)
            ·
              refine ⟨158193370767861767268200945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105462247178574511512133963 158193370767861767268200945)
              ·
                refine ⟨118645028075896325451150709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158193370767861767268200945 118645028075896325451150709)
                ·
                  refine ⟨11122971382115280511045379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 118645028075896325451150709 11122971382115280511045379)
                  ·
                    refine ⟨16684457073172920766568069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11122971382115280511045379 16684457073172920766568069)
                    ·
                      refine ⟨3128335701219922643731513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16684457073172920766568069 3128335701219922643731513)
                      ·
                        rfl

theorem cell23_6092412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_6092412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092412 prefixEnd_6092412 := by exact prefixLift 6092412
  have htrace : WordTrace (prefixWord ++ tailWord_6092412) baseStart_6092412 baseEnd_6092412 := by
    simpa [prefixWord, tailWord_6092412, baseEnd_6092412] using wordTrace_append hprefix tailTrace_6092412
  have hstable : (prefixWord ++ tailWord_6092412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092412).length < 2 ^ (prefixWord ++ tailWord_6092412).sum := by decide
  have hdescent : baseEnd_6092412 < baseStart_6092412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092446 : List Nat := [4, 3, 1, 1, 1, 3, 1, 1, 3, 1, 4]
def baseStart_6092446 : Nat := 118140960795 + 6092446 * 2 ^ 59
def prefixEnd_6092446 : Nat := 4983230072969 + 3 ^ 40 * 6092446 * 2
def baseEnd_6092446 : Nat := 3128353159562175510706357

theorem tailTrace_6092446 : CollatzResearch.WordTrace tailWord_6092446 prefixEnd_6092446 3128353159562175510706357 := by
  unfold tailWord_6092446
  simp only [CollatzResearch.WordTrace]
  refine ⟨27776220110764515472865149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148139840590744082521947461 27776220110764515472865149)
  ·
    refine ⟨10416082541536693302324431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27776220110764515472865149 10416082541536693302324431)
    ·
      refine ⟨15624123812305039953486647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10416082541536693302324431 15624123812305039953486647)
      ·
        refine ⟨23436185718457559930229971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15624123812305039953486647 23436185718457559930229971)
        ·
          refine ⟨35154278577686339895344957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23436185718457559930229971 35154278577686339895344957)
          ·
            refine ⟨13182854466632377460754359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35154278577686339895344957 13182854466632377460754359)
            ·
              refine ⟨19774281699948566191131539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13182854466632377460754359 19774281699948566191131539)
              ·
                refine ⟨29661422549922849286697309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19774281699948566191131539 29661422549922849286697309)
                ·
                  refine ⟨11123033456221068482511491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29661422549922849286697309 11123033456221068482511491)
                  ·
                    refine ⟨16684550184331602723767237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11123033456221068482511491 16684550184331602723767237)
                    ·
                      refine ⟨3128353159562175510706357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16684550184331602723767237 3128353159562175510706357)
                      ·
                        rfl

theorem cell23_6092446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_6092446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092446 prefixEnd_6092446 := by exact prefixLift 6092446
  have htrace : WordTrace (prefixWord ++ tailWord_6092446) baseStart_6092446 baseEnd_6092446 := by
    simpa [prefixWord, tailWord_6092446, baseEnd_6092446] using wordTrace_append hprefix tailTrace_6092446
  have hstable : (prefixWord ++ tailWord_6092446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092446).length < 2 ^ (prefixWord ++ tailWord_6092446).sum := by decide
  have hdescent : baseEnd_6092446 < baseStart_6092446 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092450 : List Nat := [3, 3, 1, 4, 1, 1, 2, 1, 2, 3, 2]
def baseStart_6092450 : Nat := 118140960795 + 6092450 * 2 ^ 59
def prefixEnd_6092450 : Nat := 4983230072969 + 3 ^ 40 * 6092450 * 2
def baseEnd_6092450 : Nat := 3128355213484793495056339

theorem tailTrace_6092450 : CollatzResearch.WordTrace tailWord_6092450 prefixEnd_6092450 3128355213484793495056339 := by
  unfold tailWord_6092450
  simp only [CollatzResearch.WordTrace]
  refine ⟨55552476694525408116516701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148139937852067754977377869 55552476694525408116516701)
  ·
    refine ⟨20832178760447028043693763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55552476694525408116516701 20832178760447028043693763)
    ·
      refine ⟨31248268140670542065540645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20832178760447028043693763 31248268140670542065540645)
      ·
        refine ⟨5859050276375726637288871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31248268140670542065540645 5859050276375726637288871)
        ·
          refine ⟨8788575414563589955933307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5859050276375726637288871 8788575414563589955933307)
          ·
            refine ⟨13182863121845384933899961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8788575414563589955933307 13182863121845384933899961)
            ·
              refine ⟨9887147341384038700424971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13182863121845384933899961 9887147341384038700424971)
              ·
                refine ⟨14830721012076058050637457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9887147341384038700424971 14830721012076058050637457)
                ·
                  refine ⟨11123040759057043537978093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14830721012076058050637457 11123040759057043537978093)
                  ·
                    refine ⟨4171140284646391326741785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11123040759057043537978093 4171140284646391326741785)
                    ·
                      refine ⟨3128355213484793495056339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4171140284646391326741785 3128355213484793495056339)
                      ·
                        rfl

theorem cell23_6092450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_6092450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092450 prefixEnd_6092450 := by exact prefixLift 6092450
  have htrace : WordTrace (prefixWord ++ tailWord_6092450) baseStart_6092450 baseEnd_6092450 := by
    simpa [prefixWord, tailWord_6092450, baseEnd_6092450] using wordTrace_append hprefix tailTrace_6092450
  have hstable : (prefixWord ++ tailWord_6092450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092450).length < 2 ^ (prefixWord ++ tailWord_6092450).sum := by decide
  have hdescent : baseEnd_6092450 < baseStart_6092450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092452 : List Nat := [2, 3, 1, 2, 2, 2, 2, 9]
def baseStart_6092452 : Nat := 118140960795 + 6092452 * 2 ^ 59
def prefixEnd_6092452 : Nat := 4983230072969 + 3 ^ 40 * 6092452 * 2
def baseEnd_6092452 : Nat := 115865045942448240267827

theorem tailTrace_6092452 : CollatzResearch.WordTrace tailWord_6092452 prefixEnd_6092452 115865045942448240267827 := by
  unfold tailWord_6092452
  simp only [CollatzResearch.WordTrace]
  refine ⟨111104989862047193403819805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148139986482729591205093073 111104989862047193403819805)
  ·
    refine ⟨41664371198267697526432427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111104989862047193403819805 41664371198267697526432427)
    ·
      refine ⟨62496556797401546289648641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41664371198267697526432427 62496556797401546289648641)
      ·
        refine ⟨46872417598051159717236481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62496556797401546289648641 46872417598051159717236481)
        ·
          refine ⟨35154313198538369787927361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46872417598051159717236481 35154313198538369787927361)
          ·
            refine ⟨26365734898903777340945521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35154313198538369787927361 26365734898903777340945521)
            ·
              refine ⟨19774301174177833005709141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26365734898903777340945521 19774301174177833005709141)
              ·
                refine ⟨115865045942448240267827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19774301174177833005709141 115865045942448240267827)
                ·
                  rfl

theorem cell23_6092452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 9].length) (baseStart_6092452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092452 prefixEnd_6092452 := by exact prefixLift 6092452
  have htrace : WordTrace (prefixWord ++ tailWord_6092452) baseStart_6092452 baseEnd_6092452 := by
    simpa [prefixWord, tailWord_6092452, baseEnd_6092452] using wordTrace_append hprefix tailTrace_6092452
  have hstable : (prefixWord ++ tailWord_6092452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092452).length < 2 ^ (prefixWord ++ tailWord_6092452).sum := by decide
  have hdescent : baseEnd_6092452 < baseStart_6092452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092463 : List Nat := [1, 1, 2, 1, 2, 4, 2, 5, 1, 2, 2]
def baseStart_6092463 : Nat := 118140960795 + 6092463 * 2 ^ 59
def prefixEnd_6092463 : Nat := 4983230072969 + 3 ^ 40 * 6092463 * 2
def baseEnd_6092463 : Nat := 3128361888733301944193779

theorem tailTrace_6092463 : CollatzResearch.WordTrace tailWord_6092463 prefixEnd_6092463 3128361888733301944193779 := by
  unfold tailWord_6092463
  simp only [CollatzResearch.WordTrace]
  refine ⟨222210380927054535686290043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148140253951369690457526695 222210380927054535686290043)
  ·
    refine ⟨333315571390581803529435065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222210380927054535686290043 333315571390581803529435065)
    ·
      refine ⟨249986678542936352647076299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333315571390581803529435065 249986678542936352647076299)
      ·
        refine ⟨374980017814404528970614449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249986678542936352647076299 374980017814404528970614449)
        ·
          refine ⟨281235013360803396727960837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374980017814404528970614449 281235013360803396727960837)
          ·
            refine ⟨52731565005150636886492657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 281235013360803396727960837 52731565005150636886492657)
            ·
              refine ⟨39548673753862977664869493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52731565005150636886492657 39548673753862977664869493)
              ·
                refine ⟨3707688164424654156081515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39548673753862977664869493 3707688164424654156081515)
                ·
                  refine ⟨5561532246636981234122273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3707688164424654156081515 5561532246636981234122273)
                  ·
                    refine ⟨4171149184977735925591705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5561532246636981234122273 4171149184977735925591705)
                    ·
                      refine ⟨3128361888733301944193779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4171149184977735925591705 3128361888733301944193779)
                      ·
                        rfl

theorem cell23_6092463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 5, 1, 2, 2].length) (baseStart_6092463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092463 prefixEnd_6092463 := by exact prefixLift 6092463
  have htrace : WordTrace (prefixWord ++ tailWord_6092463) baseStart_6092463 baseEnd_6092463 := by
    simpa [prefixWord, tailWord_6092463, baseEnd_6092463] using wordTrace_append hprefix tailTrace_6092463
  have hstable : (prefixWord ++ tailWord_6092463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092463).length < 2 ^ (prefixWord ++ tailWord_6092463).sum := by decide
  have hdescent : baseEnd_6092463 < baseStart_6092463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092469 : List Nat := [1, 3, 3, 3, 3, 10]
def baseStart_6092469 : Nat := 118140960795 + 6092469 * 2 ^ 59
def prefixEnd_6092469 : Nat := 4983230072969 + 3 ^ 40 * 6092469 * 2
def baseEnd_6092469 : Nat := 12873929916120283624357

theorem tailTrace_6092469 : CollatzResearch.WordTrace tailWord_6092469 prefixEnd_6092469 12873929916120283624357 := by
  unfold tailWord_6092469
  simp only [CollatzResearch.WordTrace]
  refine ⟨222210599765032798711008461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148140399843355199140672307 222210599765032798711008461)
  ·
    refine ⟨83328974911887299516628173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222210599765032798711008461 83328974911887299516628173)
    ·
      refine ⟨31248365591957737318735565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83328974911887299516628173 31248365591957737318735565)
      ·
        refine ⟨11718137096984151494525837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31248365591957737318735565 11718137096984151494525837)
        ·
          refine ⟨4394301411369056810447189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11718137096984151494525837 4394301411369056810447189)
          ·
            refine ⟨12873929916120283624357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4394301411369056810447189 12873929916120283624357)
            ·
              rfl

theorem cell23_6092469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 10].length) (baseStart_6092469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092469 prefixEnd_6092469 := by exact prefixLift 6092469
  have htrace : WordTrace (prefixWord ++ tailWord_6092469) baseStart_6092469 baseEnd_6092469 := by
    simpa [prefixWord, tailWord_6092469, baseEnd_6092469] using wordTrace_append hprefix tailTrace_6092469
  have hstable : (prefixWord ++ tailWord_6092469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092469).length < 2 ^ (prefixWord ++ tailWord_6092469).sum := by decide
  have hdescent : baseEnd_6092469 < baseStart_6092469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092493 : List Nat := [1, 6, 2, 1, 1, 2, 2, 1, 1, 2, 4]
def baseStart_6092493 : Nat := 118140960795 + 6092493 * 2 ^ 59
def prefixEnd_6092493 : Nat := 4983230072969 + 3 ^ 40 * 6092493 * 2
def baseEnd_6092493 : Nat := 3128377293152936826818641

theorem tailTrace_6092493 : CollatzResearch.WordTrace tailWord_6092493 prefixEnd_6092493 3128377293152936826818641 := by
  unfold tailWord_6092493
  simp only [CollatzResearch.WordTrace]
  refine ⟨222211475116945850809882133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148140983411297233873254755 222211475116945850809882133)
  ·
    refine ⟨10416162896106836756713225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 222211475116945850809882133 10416162896106836756713225)
    ·
      refine ⟨7812122172080127567534919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10416162896106836756713225 7812122172080127567534919)
      ·
        refine ⟨11718183258120191351302379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7812122172080127567534919 11718183258120191351302379)
        ·
          refine ⟨17577274887180287026953569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11718183258120191351302379 17577274887180287026953569)
          ·
            refine ⟨13182956165385215270215177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17577274887180287026953569 13182956165385215270215177)
            ·
              refine ⟨9887217124038911452661383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13182956165385215270215177 9887217124038911452661383)
              ·
                refine ⟨14830825686058367178992075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9887217124038911452661383 14830825686058367178992075)
                ·
                  refine ⟨22246238529087550768488113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14830825686058367178992075 22246238529087550768488113)
                  ·
                    refine ⟨16684678896815663076366085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22246238529087550768488113 16684678896815663076366085)
                    ·
                      refine ⟨3128377293152936826818641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16684678896815663076366085 3128377293152936826818641)
                      ·
                        rfl

theorem cell23_6092493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_6092493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092493 prefixEnd_6092493 := by exact prefixLift 6092493
  have htrace : WordTrace (prefixWord ++ tailWord_6092493) baseStart_6092493 baseEnd_6092493 := by
    simpa [prefixWord, tailWord_6092493, baseEnd_6092493] using wordTrace_append hprefix tailTrace_6092493
  have hstable : (prefixWord ++ tailWord_6092493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092493).length < 2 ^ (prefixWord ++ tailWord_6092493).sum := by decide
  have hdescent : baseEnd_6092493 < baseStart_6092493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092506 : List Nat := [3, 1, 1, 2, 2, 3, 2, 1, 3, 3, 2]
def baseStart_6092506 : Nat := 118140960795 + 6092506 * 2 ^ 59
def prefixEnd_6092506 : Nat := 4983230072969 + 3 ^ 40 * 6092506 * 2
def baseEnd_6092506 : Nat := 3128383968401445275956081

theorem tailTrace_6092506 : CollatzResearch.WordTrace tailWord_6092506 prefixEnd_6092506 3128383968401445275956081 := by
  unfold tailWord_6092506
  simp only [CollatzResearch.WordTrace]
  refine ⟨55552987316474688507526343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148141299510599169353403581 55552987316474688507526343)
  ·
    refine ⟨83329480974712032761289515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55552987316474688507526343 83329480974712032761289515)
    ·
      refine ⟨124994221462068049141934273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83329480974712032761289515 124994221462068049141934273)
      ·
        refine ⟨93745666096551036856450705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124994221462068049141934273 93745666096551036856450705)
        ·
          refine ⟨70309249572413277642338029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93745666096551036856450705 70309249572413277642338029)
          ·
            refine ⟨26365968589654979115876761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70309249572413277642338029 26365968589654979115876761)
            ·
              refine ⟨19774476442241234336907571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26365968589654979115876761 19774476442241234336907571)
              ·
                refine ⟨29661714663361851505361357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19774476442241234336907571 29661714663361851505361357)
                ·
                  refine ⟨11123142998760694314510509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29661714663361851505361357 11123142998760694314510509)
                  ·
                    refine ⟨4171178624535260367941441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11123142998760694314510509 4171178624535260367941441)
                    ·
                      refine ⟨3128383968401445275956081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4171178624535260367941441 3128383968401445275956081)
                      ·
                        rfl

theorem cell23_6092506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 3, 3, 2].length) (baseStart_6092506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092506 prefixEnd_6092506 := by exact prefixLift 6092506
  have htrace : WordTrace (prefixWord ++ tailWord_6092506) baseStart_6092506 baseEnd_6092506 := by
    simpa [prefixWord, tailWord_6092506, baseEnd_6092506] using wordTrace_append hprefix tailTrace_6092506
  have hstable : (prefixWord ++ tailWord_6092506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092506).length < 2 ^ (prefixWord ++ tailWord_6092506).sum := by decide
  have hdescent : baseEnd_6092506 < baseStart_6092506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092523 : List Nat := [1, 1, 1, 1, 2, 4, 6, 1, 1, 3, 2]
def baseStart_6092523 : Nat := 118140960795 + 6092523 * 2 ^ 59
def prefixEnd_6092523 : Nat := 4983230072969 + 3 ^ 40 * 6092523 * 2
def baseEnd_6092523 : Nat := 3128392697572571709443503

theorem tailTrace_6092523 : CollatzResearch.WordTrace tailWord_6092523 prefixEnd_6092523 3128392697572571709443503 := by
  unfold tailWord_6092523
  simp only [CollatzResearch.WordTrace]
  refine ⟨222212569306837165933474223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148141712871224777288982815 222212569306837165933474223)
  ·
    refine ⟨333318853960255748900211335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222212569306837165933474223 333318853960255748900211335)
    ·
      refine ⟨499978280940383623350317003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333318853960255748900211335 499978280940383623350317003)
      ·
        refine ⟨749967421410575435025475505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 499978280940383623350317003 749967421410575435025475505)
        ·
          refine ⟨562475566057931576269106629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 749967421410575435025475505 562475566057931576269106629)
          ·
            refine ⟨105464168635862170550457493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 562475566057931576269106629 105464168635862170550457493)
            ·
              refine ⟨4943632904806039244552695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 105464168635862170550457493 4943632904806039244552695)
              ·
                refine ⟨7415449357209058866829043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4943632904806039244552695 7415449357209058866829043)
                ·
                  refine ⟨11123174035813588300243565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7415449357209058866829043 11123174035813588300243565)
                  ·
                    refine ⟨4171190263430095612591337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11123174035813588300243565 4171190263430095612591337)
                    ·
                      refine ⟨3128392697572571709443503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4171190263430095612591337 3128392697572571709443503)
                      ·
                        rfl

theorem cell23_6092523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 1, 1, 3, 2].length) (baseStart_6092523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092523 prefixEnd_6092523 := by exact prefixLift 6092523
  have htrace : WordTrace (prefixWord ++ tailWord_6092523) baseStart_6092523 baseEnd_6092523 := by
    simpa [prefixWord, tailWord_6092523, baseEnd_6092523] using wordTrace_append hprefix tailTrace_6092523
  have hstable : (prefixWord ++ tailWord_6092523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092523).length < 2 ^ (prefixWord ++ tailWord_6092523).sum := by decide
  have hdescent : baseEnd_6092523 < baseStart_6092523 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092592 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 8]
def baseStart_6092592 : Nat := 118140960795 + 6092592 * 2 ^ 59
def prefixEnd_6092592 : Nat := 4983230072969 + 3 ^ 40 * 6092592 * 2
def baseEnd_6092592 : Nat := 3128428127737731939480685

theorem tailTrace_6092592 : CollatzResearch.WordTrace tailWord_6092592 prefixEnd_6092592 3128428127737731939480685 := by
  unfold tailWord_6092592
  simp only [CollatzResearch.WordTrace]
  refine ⟨111107542971793595358868015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148143390629058127145157353 111107542971793595358868015)
  ·
    refine ⟨166661314457690393038302023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111107542971793595358868015 166661314457690393038302023)
    ·
      refine ⟨249991971686535589557453035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166661314457690393038302023 249991971686535589557453035)
      ·
        refine ⟨374987957529803384336179553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249991971686535589557453035 374987957529803384336179553)
        ·
          refine ⟨281240968147352538252134665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374987957529803384336179553 281240968147352538252134665)
          ·
            refine ⟨210930726110514403689100999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281240968147352538252134665 210930726110514403689100999)
            ·
              refine ⟨316396089165771605533651499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210930726110514403689100999 316396089165771605533651499)
              ·
                refine ⟨474594133748657408300477249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 316396089165771605533651499 474594133748657408300477249)
                ·
                  refine ⟨355945600311493056225357937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 474594133748657408300477249 355945600311493056225357937)
                  ·
                    refine ⟨266959200233619792169018453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 355945600311493056225357937 266959200233619792169018453)
                    ·
                      refine ⟨3128428127737731939480685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 266959200233619792169018453 3128428127737731939480685)
                      ·
                        rfl

theorem cell23_6092592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 8].length) (baseStart_6092592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092592 prefixEnd_6092592 := by exact prefixLift 6092592
  have htrace : WordTrace (prefixWord ++ tailWord_6092592) baseStart_6092592 baseEnd_6092592 := by
    simpa [prefixWord, tailWord_6092592, baseEnd_6092592] using wordTrace_append hprefix tailTrace_6092592
  have hstable : (prefixWord ++ tailWord_6092592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092592).length < 2 ^ (prefixWord ++ tailWord_6092592).sum := by decide
  have hdescent : baseEnd_6092592 < baseStart_6092592 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092593 : List Nat := [1, 2, 2, 3, 2, 3, 3, 2, 5]
def baseStart_6092593 : Nat := 118140960795 + 6092593 * 2 ^ 59
def prefixEnd_6092593 : Nat := 4983230072969 + 3 ^ 40 * 6092593 * 2
def baseEnd_6092593 : Nat := 347603182357598492840909

theorem tailTrace_6092593 : CollatzResearch.WordTrace tailWord_6092593 prefixEnd_6092593 347603182357598492840909 := by
  unfold tailWord_6092593
  simp only [CollatzResearch.WordTrace]
  refine ⟨222215122416583567888522433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148143414944389045259014955 222215122416583567888522433)
  ·
    refine ⟨166661341812437675916391825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222215122416583567888522433 166661341812437675916391825)
    ·
      refine ⟨124996006359328256937293869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166661341812437675916391825 124996006359328256937293869)
      ·
        refine ⟨46873502384748096351485201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124996006359328256937293869 46873502384748096351485201)
        ·
          refine ⟨35155126788561072263613901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46873502384748096351485201 35155126788561072263613901)
          ·
            refine ⟨13183172545710402098855213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35155126788561072263613901 13183172545710402098855213)
            ·
              refine ⟨4943689704641400787070705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13183172545710402098855213 4943689704641400787070705)
              ·
                refine ⟨3707767278481050590303029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4943689704641400787070705 3707767278481050590303029)
                ·
                  refine ⟨347603182357598492840909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3707767278481050590303029 347603182357598492840909)
                  ·
                    rfl

theorem cell23_6092593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 2, 5].length) (baseStart_6092593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092593 prefixEnd_6092593 := by exact prefixLift 6092593
  have htrace : WordTrace (prefixWord ++ tailWord_6092593) baseStart_6092593 baseEnd_6092593 := by
    simpa [prefixWord, tailWord_6092593, baseEnd_6092593] using wordTrace_append hprefix tailTrace_6092593
  have hstable : (prefixWord ++ tailWord_6092593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092593).length < 2 ^ (prefixWord ++ tailWord_6092593).sum := by decide
  have hdescent : baseEnd_6092593 < baseStart_6092593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092626 : List Nat := [3, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4]
def baseStart_6092626 : Nat := 118140960795 + 6092626 * 2 ^ 59
def prefixEnd_6092626 : Nat := 4983230072969 + 3 ^ 40 * 6092626 * 2
def baseEnd_6092626 : Nat := 3128445586079984806455529

theorem tailTrace_6092626 : CollatzResearch.WordTrace tailWord_6092626 prefixEnd_6092626 3128445586079984806455529 := by
  unfold tailWord_6092626
  simp only [CollatzResearch.WordTrace]
  refine ⟨55554081506366003631118433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148144217350309343016315821 55554081506366003631118433)
  ·
    refine ⟨41665561129774502723338825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55554081506366003631118433 41665561129774502723338825)
    ·
      refine ⟨31249170847330877042504119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41665561129774502723338825 31249170847330877042504119)
      ·
        refine ⟨46873756270996315563756179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31249170847330877042504119 46873756270996315563756179)
        ·
          refine ⟨70310634406494473345634269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46873756270996315563756179 70310634406494473345634269)
          ·
            refine ⟨26366487902435427504612851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70310634406494473345634269 26366487902435427504612851)
            ·
              refine ⟨39549731853653141256919277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26366487902435427504612851 39549731853653141256919277)
              ·
                refine ⟨14831149445119927971344729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39549731853653141256919277 14831149445119927971344729)
                ·
                  refine ⟨11123362083839945978508547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14831149445119927971344729 11123362083839945978508547)
                  ·
                    refine ⟨16685043125759918967762821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11123362083839945978508547 16685043125759918967762821)
                    ·
                      refine ⟨3128445586079984806455529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16685043125759918967762821 3128445586079984806455529)
                      ·
                        rfl

theorem cell23_6092626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_6092626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092626 prefixEnd_6092626 := by exact prefixLift 6092626
  have htrace : WordTrace (prefixWord ++ tailWord_6092626) baseStart_6092626 baseEnd_6092626 := by
    simpa [prefixWord, tailWord_6092626, baseEnd_6092626] using wordTrace_append hprefix tailTrace_6092626
  have hstable : (prefixWord ++ tailWord_6092626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092626).length < 2 ^ (prefixWord ++ tailWord_6092626).sum := by decide
  have hdescent : baseEnd_6092626 < baseStart_6092626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092659 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 2, 5, 3]
def baseStart_6092659 : Nat := 118140960795 + 6092659 * 2 ^ 59
def prefixEnd_6092659 : Nat := 4983230072969 + 3 ^ 40 * 6092659 * 2
def baseEnd_6092659 : Nat := 3128462530941583177342877

theorem tailTrace_6092659 : CollatzResearch.WordTrace tailWord_6092659 prefixEnd_6092659 3128462530941583177342877 := by
  unfold tailWord_6092659
  simp only [CollatzResearch.WordTrace]
  refine ⟨222217529634344461160425031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148145019756229640773616687 222217529634344461160425031)
  ·
    refine ⟨333326294451516691740637547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222217529634344461160425031 333326294451516691740637547)
    ·
      refine ⟨499989441677275037610956321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333326294451516691740637547 499989441677275037610956321)
      ·
        refine ⟨374992081257956278208217241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 499989441677275037610956321 374992081257956278208217241)
        ·
          refine ⟨281244060943467208656162931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374992081257956278208217241 281244060943467208656162931)
          ·
            refine ⟨421866091415200812984244397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281244060943467208656162931 421866091415200812984244397)
            ·
              refine ⟨158199784280700304869091649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 421866091415200812984244397 158199784280700304869091649)
              ·
                refine ⟨118649838210525228651818737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158199784280700304869091649 118649838210525228651818737)
                ·
                  refine ⟨88987378657893921488864053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118649838210525228651818737 88987378657893921488864053)
                  ·
                    refine ⟨8342566749177555139581005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 88987378657893921488864053 8342566749177555139581005)
                    ·
                      refine ⟨3128462530941583177342877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8342566749177555139581005 3128462530941583177342877)
                      ·
                        rfl

theorem cell23_6092659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 5, 3].length) (baseStart_6092659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092659 prefixEnd_6092659 := by exact prefixLift 6092659
  have htrace : WordTrace (prefixWord ++ tailWord_6092659) baseStart_6092659 baseEnd_6092659 := by
    simpa [prefixWord, tailWord_6092659, baseEnd_6092659] using wordTrace_append hprefix tailTrace_6092659
  have hstable : (prefixWord ++ tailWord_6092659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092659).length < 2 ^ (prefixWord ++ tailWord_6092659).sum := by decide
  have hdescent : baseEnd_6092659 < baseStart_6092659 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092670 : List Nat := [4, 2, 3, 1, 1, 2, 1, 2, 3, 4]
def baseStart_6092670 : Nat := 118140960795 + 6092670 * 2 ^ 59
def prefixEnd_6092670 : Nat := 4983230072969 + 3 ^ 40 * 6092670 * 2
def baseEnd_6092670 : Nat := 1042822726409594211435109

theorem tailTrace_6092670 : CollatzResearch.WordTrace tailWord_6092670 prefixEnd_6092670 1042822726409594211435109 := by
  unfold tailWord_6092670
  simp only [CollatzResearch.WordTrace]
  refine ⟨27777241354663076254884433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148145287224869740026050309 27777241354663076254884433)
  ·
    refine ⟨20832931015997307191163325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27777241354663076254884433 20832931015997307191163325)
    ·
      refine ⟨7812349130998990196686247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20832931015997307191163325 7812349130998990196686247)
      ·
        refine ⟨11718523696498485295029371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7812349130998990196686247 11718523696498485295029371)
        ·
          refine ⟨17577785544747727942544057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11718523696498485295029371 17577785544747727942544057)
          ·
            refine ⟨13183339158560795956908043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17577785544747727942544057 13183339158560795956908043)
            ·
              refine ⟨19775008737841193935362065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13183339158560795956908043 19775008737841193935362065)
              ·
                refine ⟨14831256553380895451521549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19775008737841193935362065 14831256553380895451521549)
                ·
                  refine ⟨5561721207517835794320581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14831256553380895451521549 5561721207517835794320581)
                  ·
                    refine ⟨1042822726409594211435109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5561721207517835794320581 1042822726409594211435109)
                    ·
                      rfl

theorem cell23_6092670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_6092670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092670 prefixEnd_6092670 := by exact prefixLift 6092670
  have htrace : WordTrace (prefixWord ++ tailWord_6092670) baseStart_6092670 baseEnd_6092670 := by
    simpa [prefixWord, tailWord_6092670, baseEnd_6092670] using wordTrace_append hprefix tailTrace_6092670
  have hstable : (prefixWord ++ tailWord_6092670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092670).length < 2 ^ (prefixWord ++ tailWord_6092670).sum := by decide
  have hdescent : baseEnd_6092670 < baseStart_6092670 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092680 : List Nat := [2, 1, 3, 3, 3, 2, 1, 1, 2, 2, 3]
def baseStart_6092680 : Nat := 118140960795 + 6092680 * 2 ^ 59
def prefixEnd_6092680 : Nat := 4983230072969 + 3 ^ 40 * 6092680 * 2
def baseEnd_6092680 : Nat := 3128473314035327595180281

theorem tailTrace_6092680 : CollatzResearch.WordTrace tailWord_6092680 prefixEnd_6092680 3128473314035327595180281 := by
  unfold tailWord_6092680
  simp only [CollatzResearch.WordTrace]
  refine ⟨111109147783634190873469747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148145530378178921164626329 111109147783634190873469747)
  ·
    refine ⟨166663721675451286310204621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111109147783634190873469747 166663721675451286310204621)
    ·
      refine ⟨62498895628294232366326733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166663721675451286310204621 62498895628294232366326733)
      ·
        refine ⟨23437085860610337137372525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62498895628294232366326733 23437085860610337137372525)
        ·
          refine ⟨8788907197728876426514697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23437085860610337137372525 8788907197728876426514697)
          ·
            refine ⟨6591680398296657319886023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8788907197728876426514697 6591680398296657319886023)
            ·
              refine ⟨9887520597444985979829035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6591680398296657319886023 9887520597444985979829035)
              ·
                refine ⟨14831280896167478969743553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9887520597444985979829035 14831280896167478969743553)
                ·
                  refine ⟨11123460672125609227307665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14831280896167478969743553 11123460672125609227307665)
                  ·
                    refine ⟨8342595504094206920480749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11123460672125609227307665 8342595504094206920480749)
                    ·
                      refine ⟨3128473314035327595180281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8342595504094206920480749 3128473314035327595180281)
                      ·
                        rfl

theorem cell23_6092680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_6092680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092680 prefixEnd_6092680 := by exact prefixLift 6092680
  have htrace : WordTrace (prefixWord ++ tailWord_6092680) baseStart_6092680 baseEnd_6092680 := by
    simpa [prefixWord, tailWord_6092680, baseEnd_6092680] using wordTrace_append hprefix tailTrace_6092680
  have hstable : (prefixWord ++ tailWord_6092680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092680).length < 2 ^ (prefixWord ++ tailWord_6092680).sum := by decide
  have hdescent : baseEnd_6092680 < baseStart_6092680 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092709 : List Nat := [1, 3, 1, 2, 1, 1, 1, 4, 3, 6]
def baseStart_6092709 : Nat := 118140960795 + 6092709 * 2 ^ 59
def prefixEnd_6092709 : Nat := 4983230072969 + 3 ^ 40 * 6092709 * 2
def baseEnd_6092709 : Nat := 1042829401658102660572549

theorem tailTrace_6092709 : CollatzResearch.WordTrace tailWord_6092709 prefixEnd_6092709 1042829401658102660572549 := by
  unfold tailWord_6092709
  simp only [CollatzResearch.WordTrace]
  refine ⟨222219353284163319699745181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148146235522775546466496787 222219353284163319699745181)
  ·
    refine ⟨83332257481561244887404443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222219353284163319699745181 83332257481561244887404443)
    ·
      refine ⟨124998386222341867331106665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83332257481561244887404443 124998386222341867331106665)
      ·
        refine ⟨93748789666756400498329999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124998386222341867331106665 93748789666756400498329999)
        ·
          refine ⟨140623184500134600747494999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93748789666756400498329999 140623184500134600747494999)
          ·
            refine ⟨210934776750201901121242499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140623184500134600747494999 210934776750201901121242499)
            ·
              refine ⟨316402165125302851681863749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210934776750201901121242499 316402165125302851681863749)
              ·
                refine ⟨59325405960994284690349453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 316402165125302851681863749 59325405960994284690349453)
                ·
                  refine ⟨22247027235372856758881045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59325405960994284690349453 22247027235372856758881045)
                  ·
                    refine ⟨1042829401658102660572549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22247027235372856758881045 1042829401658102660572549)
                    ·
                      rfl

theorem cell23_6092709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 6].length) (baseStart_6092709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092709 prefixEnd_6092709 := by exact prefixLift 6092709
  have htrace : WordTrace (prefixWord ++ tailWord_6092709) baseStart_6092709 baseEnd_6092709 := by
    simpa [prefixWord, tailWord_6092709, baseEnd_6092709] using wordTrace_append hprefix tailTrace_6092709
  have hstable : (prefixWord ++ tailWord_6092709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092709).length < 2 ^ (prefixWord ++ tailWord_6092709).sum := by decide
  have hdescent : baseEnd_6092709 < baseStart_6092709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092716 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 4, 6, 2]
def baseStart_6092716 : Nat := 118140960795 + 6092716 * 2 ^ 59
def prefixEnd_6092716 : Nat := 4983230072969 + 3 ^ 40 * 6092716 * 2
def baseEnd_6092716 : Nat := 3128491799338889454330115

theorem tailTrace_6092716 : CollatzResearch.WordTrace tailWord_6092716 prefixEnd_6092716 3128491799338889454330115 := by
  unfold tailWord_6092716
  simp only [CollatzResearch.WordTrace]
  refine ⟨111109804297568979947625001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148146405730091973263500001 111109804297568979947625001)
  ·
    refine ⟨83332353223176734960718751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111109804297568979947625001 83332353223176734960718751)
    ·
      refine ⟨124998529834765102441078127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83332353223176734960718751 124998529834765102441078127)
      ·
        refine ⟨187497794752147653661617191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124998529834765102441078127 187497794752147653661617191)
        ·
          refine ⟨281246692128221480492425787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187497794752147653661617191 281246692128221480492425787)
          ·
            refine ⟨421870038192332220738638681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281246692128221480492425787 421870038192332220738638681)
            ·
              refine ⟨316402528644249165553979011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 421870038192332220738638681 316402528644249165553979011)
              ·
                refine ⟨474603792966373748330968517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 316402528644249165553979011 474603792966373748330968517)
                ·
                  refine ⟨88988211181195077812056597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 474603792966373748330968517 88988211181195077812056597)
                  ·
                    refine ⟨4171322399118519272440153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 88988211181195077812056597 4171322399118519272440153)
                    ·
                      refine ⟨3128491799338889454330115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4171322399118519272440153 3128491799338889454330115)
                      ·
                        rfl

theorem cell23_6092716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 6, 2].length) (baseStart_6092716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092716 prefixEnd_6092716 := by exact prefixLift 6092716
  have htrace : WordTrace (prefixWord ++ tailWord_6092716) baseStart_6092716 baseEnd_6092716 := by
    simpa [prefixWord, tailWord_6092716, baseEnd_6092716] using wordTrace_append hprefix tailTrace_6092716
  have hstable : (prefixWord ++ tailWord_6092716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092716).length < 2 ^ (prefixWord ++ tailWord_6092716).sum := by decide
  have hdescent : baseEnd_6092716 < baseStart_6092716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092733 : List Nat := [1, 4, 1, 2, 3, 1, 1, 4, 1, 1, 4]
def baseStart_6092733 : Nat := 118140960795 + 6092733 * 2 ^ 59
def prefixEnd_6092733 : Nat := 4983230072969 + 3 ^ 40 * 6092733 * 2
def baseEnd_6092733 : Nat := 3128500528510015887817537

theorem tailTrace_6092733 : CollatzResearch.WordTrace tailWord_6092733 prefixEnd_6092733 3128500528510015887817537 := by
  unfold tailWord_6092733
  simp only [CollatzResearch.WordTrace]
  refine ⟨222220228636076371798618853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148146819090717581199079235 222220228636076371798618853)
  ·
    refine ⟨41666292869264319712241035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222220228636076371798618853 41666292869264319712241035)
    ·
      refine ⟨62499439303896479568361553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41666292869264319712241035 62499439303896479568361553)
      ·
        refine ⟨46874579477922359676271165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62499439303896479568361553 46874579477922359676271165)
        ·
          refine ⟨17577967304220884878601687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46874579477922359676271165 17577967304220884878601687)
          ·
            refine ⟨26366950956331327317902531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17577967304220884878601687 26366950956331327317902531)
            ·
              refine ⟨39550426434496990976853797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26366950956331327317902531 39550426434496990976853797)
              ·
                refine ⟨7415704956468185808160087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39550426434496990976853797 7415704956468185808160087)
                ·
                  refine ⟨11123557434702278712240131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7415704956468185808160087 11123557434702278712240131)
                  ·
                    refine ⟨16685336152053418068360197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11123557434702278712240131 16685336152053418068360197)
                    ·
                      refine ⟨3128500528510015887817537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16685336152053418068360197 3128500528510015887817537)
                      ·
                        rfl

theorem cell23_6092733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_6092733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092733 prefixEnd_6092733 := by exact prefixLift 6092733
  have htrace : WordTrace (prefixWord ++ tailWord_6092733) baseStart_6092733 baseEnd_6092733 := by
    simpa [prefixWord, tailWord_6092733, baseEnd_6092733] using wordTrace_append hprefix tailTrace_6092733
  have hstable : (prefixWord ++ tailWord_6092733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092733).length < 2 ^ (prefixWord ++ tailWord_6092733).sum := by decide
  have hdescent : baseEnd_6092733 < baseStart_6092733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092746 : List Nat := [3, 1, 2, 1, 2, 1, 2, 4, 1, 2, 4]
def baseStart_6092746 : Nat := 118140960795 + 6092746 * 2 ^ 59
def prefixEnd_6092746 : Nat := 4983230072969 + 3 ^ 40 * 6092746 * 2
def baseEnd_6092746 : Nat := 3128507203758524336954977

theorem tailTrace_6092746 : CollatzResearch.WordTrace tailWord_6092746 prefixEnd_6092746 3128507203758524336954977 := by
  unfold tailWord_6092746
  simp only [CollatzResearch.WordTrace]
  refine ⟨55555175696257318754710523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148147135190019516679228061 55555175696257318754710523)
  ·
    refine ⟨83332763544385978132065785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55555175696257318754710523 83332763544385978132065785)
    ·
      refine ⟨62499572658289483599049339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83332763544385978132065785 62499572658289483599049339)
      ·
        refine ⟨93749358987434225398574009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62499572658289483599049339 93749358987434225398574009)
        ·
          refine ⟨70312019240575669048930507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93749358987434225398574009 70312019240575669048930507)
          ·
            refine ⟨105468028860863503573395761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70312019240575669048930507 105468028860863503573395761)
            ·
              refine ⟨79101021645647627680046821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105468028860863503573395761 79101021645647627680046821)
              ·
                refine ⟨14831441558558930190008779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79101021645647627680046821 14831441558558930190008779)
                ·
                  refine ⟨22247162337838395285013169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14831441558558930190008779 22247162337838395285013169)
                  ·
                    refine ⟨16685371753378796463759877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22247162337838395285013169 16685371753378796463759877)
                    ·
                      refine ⟨3128507203758524336954977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16685371753378796463759877 3128507203758524336954977)
                      ·
                        rfl

theorem cell23_6092746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_6092746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092746 prefixEnd_6092746 := by exact prefixLift 6092746
  have htrace : WordTrace (prefixWord ++ tailWord_6092746) baseStart_6092746 baseEnd_6092746 := by
    simpa [prefixWord, tailWord_6092746, baseEnd_6092746] using wordTrace_append hprefix tailTrace_6092746
  have hstable : (prefixWord ++ tailWord_6092746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092746).length < 2 ^ (prefixWord ++ tailWord_6092746).sum := by decide
  have hdescent : baseEnd_6092746 < baseStart_6092746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092767 : List Nat := [1, 1, 2, 3, 4, 3, 1, 1, 3, 2, 2]
def baseStart_6092767 : Nat := 118140960795 + 6092767 * 2 ^ 59
def prefixEnd_6092767 : Nat := 4983230072969 + 3 ^ 40 * 6092767 * 2
def baseEnd_6092767 : Nat := 3128517986852268754792381

theorem tailTrace_6092767 : CollatzResearch.WordTrace tailWord_6092767 prefixEnd_6092767 3128517986852268754792381 := by
  unfold tailWord_6092767
  simp only [CollatzResearch.WordTrace]
  refine ⟨222221468717953195605356555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148147645811968797070237703 222221468717953195605356555)
  ·
    refine ⟨333332203076929793408034833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222221468717953195605356555 333332203076929793408034833)
    ·
      refine ⟨249999152307697345056026125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333332203076929793408034833 249999152307697345056026125)
      ·
        refine ⟨93749682115386504396009797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249999152307697345056026125 93749682115386504396009797)
        ·
          refine ⟨17578065396634969574251837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93749682115386504396009797 17578065396634969574251837)
          ·
            refine ⟨6591774523738113590344439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17578065396634969574251837 6591774523738113590344439)
            ·
              refine ⟨9887661785607170385516659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6591774523738113590344439 9887661785607170385516659)
              ·
                refine ⟨14831492678410755578274989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9887661785607170385516659 14831492678410755578274989)
                ·
                  refine ⟨5561809754404033341853121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14831492678410755578274989 5561809754404033341853121)
                  ·
                    refine ⟨4171357315803025006389841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5561809754404033341853121 4171357315803025006389841)
                    ·
                      refine ⟨3128517986852268754792381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4171357315803025006389841 3128517986852268754792381)
                      ·
                        rfl

theorem cell23_6092767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 3, 2, 2].length) (baseStart_6092767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092767 prefixEnd_6092767 := by exact prefixLift 6092767
  have htrace : WordTrace (prefixWord ++ tailWord_6092767) baseStart_6092767 baseEnd_6092767 := by
    simpa [prefixWord, tailWord_6092767, baseEnd_6092767] using wordTrace_append hprefix tailTrace_6092767
  have hstable : (prefixWord ++ tailWord_6092767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092767).length < 2 ^ (prefixWord ++ tailWord_6092767).sum := by decide
  have hdescent : baseEnd_6092767 < baseStart_6092767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092804 : List Nat := [2, 3, 2, 4, 1, 1, 3, 1, 1, 2, 3]
def baseStart_6092804 : Nat := 118140960795 + 6092804 * 2 ^ 59
def prefixEnd_6092804 : Nat := 4983230072969 + 3 ^ 40 * 6092804 * 2
def baseEnd_6092804 : Nat := 3128536985636485110029711

theorem tailTrace_6092804 : CollatzResearch.WordTrace tailWord_6092804 prefixEnd_6092804 3128536985636485110029711 := by
  unfold tailWord_6092804
  simp only [CollatzResearch.WordTrace]
  refine ⟨111111409109409575462226733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148148545479212767282968977 111111409109409575462226733)
  ·
    refine ⟨41666778416028590798335025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111111409109409575462226733 41666778416028590798335025)
    ·
      refine ⟨31250083812021443098751269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41666778416028590798335025 31250083812021443098751269)
      ·
        refine ⟨5859390714754020581015863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31250083812021443098751269 5859390714754020581015863)
        ·
          refine ⟨8789086072131030871523795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5859390714754020581015863 8789086072131030871523795)
          ·
            refine ⟨13183629108196546307285693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8789086072131030871523795 13183629108196546307285693)
            ·
              refine ⟨4943860915573704865232135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13183629108196546307285693 4943860915573704865232135)
              ·
                refine ⟨7415791373360557297848203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4943860915573704865232135 7415791373360557297848203)
                ·
                  refine ⟨11123687060040835946772305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7415791373360557297848203 11123687060040835946772305)
                  ·
                    refine ⟨8342765295030626960079229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11123687060040835946772305 8342765295030626960079229)
                    ·
                      refine ⟨3128536985636485110029711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8342765295030626960079229 3128536985636485110029711)
                      ·
                        rfl

theorem cell23_6092804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_6092804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092804 prefixEnd_6092804 := by exact prefixLift 6092804
  have htrace : WordTrace (prefixWord ++ tailWord_6092804) baseStart_6092804 baseEnd_6092804 := by
    simpa [prefixWord, tailWord_6092804, baseEnd_6092804] using wordTrace_append hprefix tailTrace_6092804
  have hstable : (prefixWord ++ tailWord_6092804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092804).length < 2 ^ (prefixWord ++ tailWord_6092804).sum := by decide
  have hdescent : baseEnd_6092804 < baseStart_6092804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092833 : List Nat := [1, 2, 3, 2, 4, 1, 1, 1, 2, 6]
def baseStart_6092833 : Nat := 118140960795 + 6092833 * 2 ^ 59
def prefixEnd_6092833 : Nat := 4983230072969 + 3 ^ 40 * 6092833 * 2
def baseEnd_6092833 : Nat := 1042850625525155165522359

theorem tailTrace_6092833 : CollatzResearch.WordTrace tailWord_6092833 prefixEnd_6092833 1042850625525155165522359 := by
  unfold tailWord_6092833
  simp only [CollatzResearch.WordTrace]
  refine ⟨222223875935714088877259153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148149250623809392584839435 222223875935714088877259153)
  ·
    refine ⟨166667906951785566657944365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222223875935714088877259153 166667906951785566657944365)
    ·
      refine ⟨62500465106919587496729137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166667906951785566657944365 62500465106919587496729137)
      ·
        refine ⟨46875348830189690622546853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62500465106919587496729137 46875348830189690622546853)
        ·
          refine ⟨8789127905660566991727535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46875348830189690622546853 8789127905660566991727535)
          ·
            refine ⟨13183691858490850487591303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8789127905660566991727535 13183691858490850487591303)
            ·
              refine ⟨19775537787736275731386955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13183691858490850487591303 19775537787736275731386955)
              ·
                refine ⟨29663306681604413597080433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19775537787736275731386955 29663306681604413597080433)
                ·
                  refine ⟨22247480011203310197810325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29663306681604413597080433 22247480011203310197810325)
                  ·
                    refine ⟨1042850625525155165522359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22247480011203310197810325 1042850625525155165522359)
                    ·
                      rfl

theorem cell23_6092833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 6].length) (baseStart_6092833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092833 prefixEnd_6092833 := by exact prefixLift 6092833
  have htrace : WordTrace (prefixWord ++ tailWord_6092833) baseStart_6092833 baseEnd_6092833 := by
    simpa [prefixWord, tailWord_6092833, baseEnd_6092833] using wordTrace_append hprefix tailTrace_6092833
  have hstable : (prefixWord ++ tailWord_6092833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092833).length < 2 ^ (prefixWord ++ tailWord_6092833).sum := by decide
  have hdescent : baseEnd_6092833 < baseStart_6092833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092863 : List Nat := [1, 1, 2, 2, 3, 1, 3, 5, 5]
def baseStart_6092863 : Nat := 118140960795 + 6092863 * 2 ^ 59
def prefixEnd_6092863 : Nat := 4983230072969 + 3 ^ 40 * 6092863 * 2
def baseEnd_6092863 : Nat := 347618586777233375465771

theorem tailTrace_6092863 : CollatzResearch.WordTrace tailWord_6092863 prefixEnd_6092863 347618586777233375465771 := by
  unfold tailWord_6092863
  simp only [CollatzResearch.WordTrace]
  refine ⟨222224970125605404000851243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148149980083736936000567495 222224970125605404000851243)
  ·
    refine ⟨333337455188408106001276865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222224970125605404000851243 333337455188408106001276865)
    ·
      refine ⟨250003091391306079500957649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333337455188408106001276865 250003091391306079500957649)
      ·
        refine ⟨187502318543479559625718237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250003091391306079500957649 187502318543479559625718237)
        ·
          refine ⟨70313369453804834859644339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187502318543479559625718237 70313369453804834859644339)
          ·
            refine ⟨105470054180707252289466509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70313369453804834859644339 105470054180707252289466509)
            ·
              refine ⟨39551270317765219608549941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105470054180707252289466509 39551270317765219608549941)
              ·
                refine ⟨3707931592290489338301557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39551270317765219608549941 3707931592290489338301557)
                ·
                  refine ⟨347618586777233375465771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3707931592290489338301557 347618586777233375465771)
                  ·
                    rfl

theorem cell23_6092863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 5, 5].length) (baseStart_6092863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092863 prefixEnd_6092863 := by exact prefixLift 6092863
  have htrace : WordTrace (prefixWord ++ tailWord_6092863) baseStart_6092863 baseEnd_6092863 := by
    simpa [prefixWord, tailWord_6092863, baseEnd_6092863] using wordTrace_append hprefix tailTrace_6092863
  have hstable : (prefixWord ++ tailWord_6092863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092863).length < 2 ^ (prefixWord ++ tailWord_6092863).sum := by decide
  have hdescent : baseEnd_6092863 < baseStart_6092863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092870 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4]
def baseStart_6092870 : Nat := 118140960795 + 6092870 * 2 ^ 59
def prefixEnd_6092870 : Nat := 4983230072969 + 3 ^ 40 * 6092870 * 2
def baseEnd_6092870 : Nat := 3128570875359681851804407

theorem tailTrace_6092870 : CollatzResearch.WordTrace tailWord_6092870 prefixEnd_6092870 3128570875359681851804407 := by
  unfold tailWord_6092870
  simp only [CollatzResearch.WordTrace]
  refine ⟨6944538294893126381136127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 148150150291053362797570709 6944538294893126381136127)
  ·
    refine ⟨10416807442339689571704191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6944538294893126381136127 10416807442339689571704191)
    ·
      refine ⟨15625211163509534357556287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10416807442339689571704191 15625211163509534357556287)
      ·
        refine ⟨23437816745264301536334431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15625211163509534357556287 23437816745264301536334431)
        ·
          refine ⟨35156725117896452304501647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23437816745264301536334431 35156725117896452304501647)
          ·
            refine ⟨52735087676844678456752471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35156725117896452304501647 52735087676844678456752471)
            ·
              refine ⟨79102631515267017685128707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52735087676844678456752471 79102631515267017685128707)
              ·
                refine ⟨118653947272900526527693061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79102631515267017685128707 118653947272900526527693061)
                ·
                  refine ⟨22247615113668848723942449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 118653947272900526527693061 22247615113668848723942449)
                  ·
                    refine ⟨16685711335251636542956837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22247615113668848723942449 16685711335251636542956837)
                    ·
                      refine ⟨3128570875359681851804407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16685711335251636542956837 3128570875359681851804407)
                      ·
                        rfl

theorem cell23_6092870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_6092870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092870 prefixEnd_6092870 := by exact prefixLift 6092870
  have htrace : WordTrace (prefixWord ++ tailWord_6092870) baseStart_6092870 baseEnd_6092870 := by
    simpa [prefixWord, tailWord_6092870, baseEnd_6092870] using wordTrace_append hprefix tailTrace_6092870
  have hstable : (prefixWord ++ tailWord_6092870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092870).length < 2 ^ (prefixWord ++ tailWord_6092870).sum := by decide
  have hdescent : baseEnd_6092870 < baseStart_6092870 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6092913 : List Nat := [1, 2, 2, 2, 1, 1, 4, 3, 2, 1, 4]
def baseStart_6092913 : Nat := 118140960795 + 6092913 * 2 ^ 59
def prefixEnd_6092913 : Nat := 4983230072969 + 3 ^ 40 * 6092913 * 2
def baseEnd_6092913 : Nat := 3128592955027825183566709

theorem tailTrace_6092913 : CollatzResearch.WordTrace tailWord_6092913 prefixEnd_6092913 3128592955027825183566709 := by
  unfold tailWord_6092913
  simp only [CollatzResearch.WordTrace]
  refine ⟨222226793775424262540171393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148151195850282841693447595 222226793775424262540171393)
  ·
    refine ⟨166670095331568196905128545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222226793775424262540171393 166670095331568196905128545)
    ·
      refine ⟨125002571498676147678846409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166670095331568196905128545 125002571498676147678846409)
      ·
        refine ⟨93751928624007110759134807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125002571498676147678846409 93751928624007110759134807)
        ·
          refine ⟨140627892936010666138702211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93751928624007110759134807 140627892936010666138702211)
          ·
            refine ⟨210941839404015999208053317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140627892936010666138702211 210941839404015999208053317)
            ·
              refine ⟨39551594888252999851509997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 210941839404015999208053317 39551594888252999851509997)
              ·
                refine ⟨14831848083094874944316249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39551594888252999851509997 14831848083094874944316249)
                ·
                  refine ⟨11123886062321156208237187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14831848083094874944316249 11123886062321156208237187)
                  ·
                    refine ⟨16685829093481734312355781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11123886062321156208237187 16685829093481734312355781)
                    ·
                      refine ⟨3128592955027825183566709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16685829093481734312355781 3128592955027825183566709)
                      ·
                        rfl

theorem cell23_6092913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_6092913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6092913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6092913 prefixEnd_6092913 := by exact prefixLift 6092913
  have htrace : WordTrace (prefixWord ++ tailWord_6092913) baseStart_6092913 baseEnd_6092913 := by
    simpa [prefixWord, tailWord_6092913, baseEnd_6092913] using wordTrace_append hprefix tailTrace_6092913
  have hstable : (prefixWord ++ tailWord_6092913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6092913).length < 2 ^ (prefixWord ++ tailWord_6092913).sum := by decide
  have hdescent : baseEnd_6092913 < baseStart_6092913 := by decide
  rcases family_descends (prefixWord ++ tailWord_6092913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093003 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 5, 1, 4]
def baseStart_6093003 : Nat := 118140960795 + 6093003 * 2 ^ 59
def prefixEnd_6093003 : Nat := 4983230072969 + 3 ^ 40 * 6093003 * 2
def baseEnd_6093003 : Nat := 3128639168286729831441295

theorem tailTrace_6093003 : CollatzResearch.WordTrace tailWord_6093003 prefixEnd_6093003 3128639168286729831441295 := by
  unfold tailWord_6093003
  simp only [CollatzResearch.WordTrace]
  refine ⟨222230076345098207910947663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148153384230065471940631775 222230076345098207910947663)
  ·
    refine ⟨333345114517647311866421495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222230076345098207910947663 333345114517647311866421495)
    ·
      refine ⟨500017671776470967799632243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333345114517647311866421495 500017671776470967799632243)
      ·
        refine ⟨750026507664706451699448365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500017671776470967799632243 750026507664706451699448365)
        ·
          refine ⟨281259940374264919387293137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 750026507664706451699448365 281259940374264919387293137)
          ·
            refine ⟨210944955280698689540469853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281259940374264919387293137 210944955280698689540469853)
            ·
              refine ⟨79104358230262008577676195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 210944955280698689540469853 79104358230262008577676195)
              ·
                refine ⟨118656537345393012866514293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79104358230262008577676195 118656537345393012866514293)
                ·
                  refine ⟨11124050376130594956235715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 118656537345393012866514293 11124050376130594956235715)
                  ·
                    refine ⟨16686075564195892434353573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11124050376130594956235715 16686075564195892434353573)
                    ·
                      refine ⟨3128639168286729831441295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16686075564195892434353573 3128639168286729831441295)
                      ·
                        rfl

theorem cell23_6093003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 5, 1, 4].length) (baseStart_6093003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093003 prefixEnd_6093003 := by exact prefixLift 6093003
  have htrace : WordTrace (prefixWord ++ tailWord_6093003) baseStart_6093003 baseEnd_6093003 := by
    simpa [prefixWord, tailWord_6093003, baseEnd_6093003] using wordTrace_append hprefix tailTrace_6093003
  have hstable : (prefixWord ++ tailWord_6093003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093003).length < 2 ^ (prefixWord ++ tailWord_6093003).sum := by decide
  have hdescent : baseEnd_6093003 < baseStart_6093003 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093014 : List Nat := [5, 2, 1, 2, 1, 1, 1, 1, 5, 1, 3]
def baseStart_6093014 : Nat := 118140960795 + 6093014 * 2 ^ 59
def prefixEnd_6093014 : Nat := 4983230072969 + 3 ^ 40 * 6093014 * 2
def baseEnd_6093014 : Nat := 3128644816573929288403745

theorem tailTrace_6093014 : CollatzResearch.WordTrace tailWord_6093014 prefixEnd_6093014 3128644816573929288403745 := by
  unfold tailWord_6093014
  simp only [CollatzResearch.WordTrace]
  refine ⟨13889404846753647299349881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148153651698705571193065397 13889404846753647299349881)
  ·
    refine ⟨10417053635065235474512411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13889404846753647299349881 10417053635065235474512411)
    ·
      refine ⟨15625580452597853211768617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10417053635065235474512411 15625580452597853211768617)
      ·
        refine ⟨11719185339448389908826463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15625580452597853211768617 11719185339448389908826463)
        ·
          refine ⟨17578778009172584863239695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11719185339448389908826463 17578778009172584863239695)
          ·
            refine ⟨26368167013758877294859543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17578778009172584863239695 26368167013758877294859543)
            ·
              refine ⟨39552250520638315942289315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26368167013758877294859543 39552250520638315942289315)
              ·
                refine ⟨59328375780957473913433973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39552250520638315942289315 59328375780957473913433973)
                ·
                  refine ⟨5562035229464763179384435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59328375780957473913433973 5562035229464763179384435)
                  ·
                    refine ⟨8343052844197144769076653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5562035229464763179384435 8343052844197144769076653)
                    ·
                      refine ⟨3128644816573929288403745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8343052844197144769076653 3128644816573929288403745)
                      ·
                        rfl

theorem cell23_6093014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_6093014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093014 prefixEnd_6093014 := by exact prefixLift 6093014
  have htrace : WordTrace (prefixWord ++ tailWord_6093014) baseStart_6093014 baseEnd_6093014 := by
    simpa [prefixWord, tailWord_6093014, baseEnd_6093014] using wordTrace_append hprefix tailTrace_6093014
  have hstable : (prefixWord ++ tailWord_6093014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093014).length < 2 ^ (prefixWord ++ tailWord_6093014).sum := by decide
  have hdescent : baseEnd_6093014 < baseStart_6093014 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093031 : List Nat := [1, 1, 5, 3, 1, 2, 2, 3, 1, 1, 3]
def baseStart_6093031 : Nat := 118140960795 + 6093031 * 2 ^ 59
def prefixEnd_6093031 : Nat := 4983230072969 + 3 ^ 40 * 6093031 * 2
def baseEnd_6093031 : Nat := 3128653545745055721891167

theorem tailTrace_6093031 : CollatzResearch.WordTrace tailWord_6093031 prefixEnd_6093031 3128653545745055721891167 := by
  unfold tailWord_6093031
  simp only [CollatzResearch.WordTrace]
  refine ⟨222231097588996768692966947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148154065059331179128644631 222231097588996768692966947)
  ·
    refine ⟨333346646383495153039450421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222231097588996768692966947 333346646383495153039450421)
    ·
      refine ⟨31251248098452670597448477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 333346646383495153039450421 31251248098452670597448477)
      ·
        refine ⟨11719218036919751474043179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31251248098452670597448477 11719218036919751474043179)
        ·
          refine ⟨17578827055379627211064769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11719218036919751474043179 17578827055379627211064769)
          ·
            refine ⟨13184120291534720408298577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17578827055379627211064769 13184120291534720408298577)
            ·
              refine ⟨9888090218651040306223933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13184120291534720408298577 9888090218651040306223933)
              ·
                refine ⟨3708033831994140114833975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9888090218651040306223933 3708033831994140114833975)
                ·
                  refine ⟨5562050747991210172250963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3708033831994140114833975 5562050747991210172250963)
                  ·
                    refine ⟨8343076121986815258376445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5562050747991210172250963 8343076121986815258376445)
                    ·
                      refine ⟨3128653545745055721891167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8343076121986815258376445 3128653545745055721891167)
                      ·
                        rfl

theorem cell23_6093031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_6093031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093031 prefixEnd_6093031 := by exact prefixLift 6093031
  have htrace : WordTrace (prefixWord ++ tailWord_6093031) baseStart_6093031 baseEnd_6093031 := by
    simpa [prefixWord, tailWord_6093031, baseEnd_6093031] using wordTrace_append hprefix tailTrace_6093031
  have hstable : (prefixWord ++ tailWord_6093031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093031).length < 2 ^ (prefixWord ++ tailWord_6093031).sum := by decide
  have hdescent : baseEnd_6093031 < baseStart_6093031 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093064 : List Nat := [2, 1, 3, 2, 3, 2, 3, 1, 2, 4]
def baseStart_6093064 : Nat := 118140960795 + 6093064 * 2 ^ 59
def prefixEnd_6093064 : Nat := 4983230072969 + 3 ^ 40 * 6093064 * 2
def baseEnd_6093064 : Nat := 1042890163535551364259505

theorem tailTrace_6093064 : CollatzResearch.WordTrace tailWord_6093064 prefixEnd_6093064 1042890163535551364259505 := by
  unfold tailWord_6093064
  simp only [CollatzResearch.WordTrace]
  refine ⟨111116150598938607664459123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148154867465251476885945497 111116150598938607664459123)
  ·
    refine ⟨166674225898407911496688685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111116150598938607664459123 166674225898407911496688685)
    ·
      refine ⟨62502834711902966811258257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166674225898407911496688685 62502834711902966811258257)
      ·
        refine ⟨46877126033927225108443693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62502834711902966811258257 46877126033927225108443693)
        ·
          refine ⟨17578922262722709415666385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46877126033927225108443693 17578922262722709415666385)
          ·
            refine ⟨13184191697042032061749789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17578922262722709415666385 13184191697042032061749789)
            ·
              refine ⟨4944071886390762023156171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13184191697042032061749789 4944071886390762023156171)
              ·
                refine ⟨7416107829586143034734257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4944071886390762023156171 7416107829586143034734257)
                ·
                  refine ⟨5562080872189607276050693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7416107829586143034734257 5562080872189607276050693)
                  ·
                    refine ⟨1042890163535551364259505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5562080872189607276050693 1042890163535551364259505)
                    ·
                      rfl

theorem cell23_6093064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 1, 2, 4].length) (baseStart_6093064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093064 prefixEnd_6093064 := by exact prefixLift 6093064
  have htrace : WordTrace (prefixWord ++ tailWord_6093064) baseStart_6093064 baseEnd_6093064 := by
    simpa [prefixWord, tailWord_6093064, baseEnd_6093064] using wordTrace_append hprefix tailTrace_6093064
  have hstable : (prefixWord ++ tailWord_6093064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093064).length < 2 ^ (prefixWord ++ tailWord_6093064).sum := by decide
  have hdescent : baseEnd_6093064 < baseStart_6093064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093083 : List Nat := [1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 5]
def baseStart_6093083 : Nat := 118140960795 + 6093083 * 2 ^ 59
def prefixEnd_6093083 : Nat := 4983230072969 + 3 ^ 40 * 6093083 * 2
def baseEnd_6093083 : Nat := 3128680246739089518440927

theorem tailTrace_6093083 : CollatzResearch.WordTrace tailWord_6093083 prefixEnd_6093083 3128680246739089518440927 := by
  unfold tailWord_6093083
  simp only [CollatzResearch.WordTrace]
  refine ⟨222232994184808381573859903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148155329456538921049239935 222232994184808381573859903)
  ·
    refine ⟨333349491277212572360789855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222232994184808381573859903 333349491277212572360789855)
    ·
      refine ⟨500024236915818858541184783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333349491277212572360789855 500024236915818858541184783)
      ·
        refine ⟨750036355373728287811777175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500024236915818858541184783 750036355373728287811777175)
        ·
          refine ⟨1125054533060592431717665763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 750036355373728287811777175 1125054533060592431717665763)
          ·
            refine ⟨1687581799590888647576498645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1125054533060592431717665763 1687581799590888647576498645)
            ·
              refine ⟨39552698427911452677574187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1687581799590888647576498645 39552698427911452677574187)
              ·
                refine ⟨59329047641867179016361281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39552698427911452677574187 59329047641867179016361281)
                ·
                  refine ⟨44496785731400384262270961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59329047641867179016361281 44496785731400384262270961)
                  ·
                    refine ⟨33372589298550288196703221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44496785731400384262270961 33372589298550288196703221)
                    ·
                      refine ⟨3128680246739089518440927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33372589298550288196703221 3128680246739089518440927)
                      ·
                        rfl

theorem cell23_6093083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 5].length) (baseStart_6093083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093083 prefixEnd_6093083 := by exact prefixLift 6093083
  have htrace : WordTrace (prefixWord ++ tailWord_6093083) baseStart_6093083 baseEnd_6093083 := by
    simpa [prefixWord, tailWord_6093083, baseEnd_6093083] using wordTrace_append hprefix tailTrace_6093083
  have hstable : (prefixWord ++ tailWord_6093083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093083).length < 2 ^ (prefixWord ++ tailWord_6093083).sum := by decide
  have hdescent : baseEnd_6093083 < baseStart_6093083 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093087 : List Nat := [1, 1, 2, 4, 3, 1, 1, 2, 4, 1, 3]
def baseStart_6093087 : Nat := 118140960795 + 6093087 * 2 ^ 59
def prefixEnd_6093087 : Nat := 4983230072969 + 3 ^ 40 * 6093087 * 2
def baseEnd_6093087 : Nat := 3128682300661707502790909

theorem tailTrace_6093087 : CollatzResearch.WordTrace tailWord_6093087 prefixEnd_6093087 3128682300661707502790909 := by
  unfold tailWord_6093087
  simp only [CollatzResearch.WordTrace]
  refine ⟨222233140076793890257005515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148155426717862593504670343 222233140076793890257005515)
  ·
    refine ⟨333349710115190835385508273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222233140076793890257005515 333349710115190835385508273)
    ·
      refine ⟨250012282586393126539131205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333349710115190835385508273 250012282586393126539131205)
      ·
        refine ⟨46877302984948711226087101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 250012282586393126539131205 46877302984948711226087101)
        ·
          refine ⟨17578988619355766709782663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46877302984948711226087101 17578988619355766709782663)
          ·
            refine ⟨26368482929033650064673995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17578988619355766709782663 26368482929033650064673995)
            ·
              refine ⟨39552724393550475097010993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26368482929033650064673995 39552724393550475097010993)
              ·
                refine ⟨29664543295162856322758245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39552724393550475097010993 29664543295162856322758245)
                ·
                  refine ⟨5562101867843035560517171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29664543295162856322758245 5562101867843035560517171)
                  ·
                    refine ⟨8343152801764553340775757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5562101867843035560517171 8343152801764553340775757)
                    ·
                      refine ⟨3128682300661707502790909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8343152801764553340775757 3128682300661707502790909)
                      ·
                        rfl

theorem cell23_6093087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_6093087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093087 prefixEnd_6093087 := by exact prefixLift 6093087
  have htrace : WordTrace (prefixWord ++ tailWord_6093087) baseStart_6093087 baseEnd_6093087 := by
    simpa [prefixWord, tailWord_6093087, baseEnd_6093087] using wordTrace_append hprefix tailTrace_6093087
  have hstable : (prefixWord ++ tailWord_6093087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093087).length < 2 ^ (prefixWord ++ tailWord_6093087).sum := by decide
  have hdescent : baseEnd_6093087 < baseStart_6093087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093088 : List Nat := [2, 1, 1, 5, 2, 3, 1, 3, 1, 2, 2]
def baseStart_6093088 : Nat := 118140960795 + 6093088 * 2 ^ 59
def prefixEnd_6093088 : Nat := 4983230072969 + 3 ^ 40 * 6093088 * 2
def baseEnd_6093088 : Nat := 3128682814142361998878405

theorem tailTrace_6093088 : CollatzResearch.WordTrace tailWord_6093088 prefixEnd_6093088 3128682814142361998878405 := by
  unfold tailWord_6093088
  simp only [CollatzResearch.WordTrace]
  refine ⟨111116588274895133713895959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148155451033193511618527945 111116588274895133713895959)
  ·
    refine ⟨166674882412342700570843939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111116588274895133713895959 166674882412342700570843939)
    ·
      refine ⟨250012323618514050856265909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166674882412342700570843939 250012323618514050856265909)
      ·
        refine ⟨23438655339235692267774929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 250012323618514050856265909 23438655339235692267774929)
        ·
          refine ⟨17578991504426769200831197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23438655339235692267774929 17578991504426769200831197)
          ·
            refine ⟨6592121814160038450311699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17578991504426769200831197 6592121814160038450311699)
            ·
              refine ⟨9888182721240057675467549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6592121814160038450311699 9888182721240057675467549)
              ·
                refine ⟨3708068520465021628300331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9888182721240057675467549 3708068520465021628300331)
                ·
                  refine ⟨5562102780697532442450497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3708068520465021628300331 5562102780697532442450497)
                  ·
                    refine ⟨4171577085523149331837873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5562102780697532442450497 4171577085523149331837873)
                    ·
                      refine ⟨3128682814142361998878405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4171577085523149331837873 3128682814142361998878405)
                      ·
                        rfl

theorem cell23_6093088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_6093088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093088 prefixEnd_6093088 := by exact prefixLift 6093088
  have htrace : WordTrace (prefixWord ++ tailWord_6093088) baseStart_6093088 baseEnd_6093088 := by
    simpa [prefixWord, tailWord_6093088, baseEnd_6093088] using wordTrace_append hprefix tailTrace_6093088
  have hstable : (prefixWord ++ tailWord_6093088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093088).length < 2 ^ (prefixWord ++ tailWord_6093088).sum := by decide
  have hdescent : baseEnd_6093088 < baseStart_6093088 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093103 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 4, 6]
def baseStart_6093103 : Nat := 118140960795 + 6093103 * 2 ^ 59
def prefixEnd_6093103 : Nat := 4983230072969 + 3 ^ 40 * 6093103 * 2
def baseEnd_6093103 : Nat := 1042896838784059813396945

theorem tailTrace_6093103 : CollatzResearch.WordTrace tailWord_6093103 prefixEnd_6093103 1042896838784059813396945 := by
  unfold tailWord_6093103
  simp only [CollatzResearch.WordTrace]
  refine ⟨222233723644735924989587963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148155815763157283326391975 222233723644735924989587963)
  ·
    refine ⟨333350585467103887484381945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222233723644735924989587963 333350585467103887484381945)
    ·
      refine ⟨250012939100327915613286459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333350585467103887484381945 250012939100327915613286459)
      ·
        refine ⟨375019408650491873419929689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250012939100327915613286459 375019408650491873419929689)
        ·
          refine ⟨281264556487868905064947267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 375019408650491873419929689 281264556487868905064947267)
          ·
            refine ⟨421896834731803357597420901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281264556487868905064947267 421896834731803357597420901)
            ·
              refine ⟨79105656512213129549516419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 421896834731803357597420901 79105656512213129549516419)
              ·
                refine ⟨118658484768319694324274629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79105656512213129549516419 118658484768319694324274629)
                ·
                  refine ⟨22248465894059942685801493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 118658484768319694324274629 22248465894059942685801493)
                  ·
                    refine ⟨1042896838784059813396945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22248465894059942685801493 1042896838784059813396945)
                    ·
                      rfl

theorem cell23_6093103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 6].length) (baseStart_6093103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093103 prefixEnd_6093103 := by exact prefixLift 6093103
  have htrace : WordTrace (prefixWord ++ tailWord_6093103) baseStart_6093103 baseEnd_6093103 := by
    simpa [prefixWord, tailWord_6093103, baseEnd_6093103] using wordTrace_append hprefix tailTrace_6093103
  have hstable : (prefixWord ++ tailWord_6093103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093103).length < 2 ^ (prefixWord ++ tailWord_6093103).sum := by decide
  have hdescent : baseEnd_6093103 < baseStart_6093103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093121 : List Nat := [1, 2, 5, 2, 2, 1, 1, 3, 2, 1, 3]
def baseStart_6093121 : Nat := 118140960795 + 6093121 * 2 ^ 59
def prefixEnd_6093121 : Nat := 4983230072969 + 3 ^ 40 * 6093121 * 2
def baseEnd_6093121 : Nat := 3128699759003960369765753

theorem tailTrace_6093121 : CollatzResearch.WordTrace tailWord_6093121 prefixEnd_6093121 3128699759003960369765753 := by
  unfold tailWord_6093121
  simp only [CollatzResearch.WordTrace]
  refine ⟨222234380158670714063743217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148156253439113809375828811 222234380158670714063743217)
  ·
    refine ⟨166675785119003035547807413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222234380158670714063743217 166675785119003035547807413)
    ·
      refine ⟨15625854854906534582606945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 166675785119003035547807413 15625854854906534582606945)
      ·
        refine ⟨11719391141179900936955209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15625854854906534582606945 11719391141179900936955209)
        ·
          refine ⟨8789543355884925702716407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11719391141179900936955209 8789543355884925702716407)
          ·
            refine ⟨13184315033827388554074611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8789543355884925702716407 13184315033827388554074611)
            ·
              refine ⟨19776472550741082831111917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13184315033827388554074611 19776472550741082831111917)
              ·
                refine ⟨7416177206527906061666969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19776472550741082831111917 7416177206527906061666969)
                ·
                  refine ⟨5562132904895929546250227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7416177206527906061666969 5562132904895929546250227)
                  ·
                    refine ⟨8343199357343894319375341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5562132904895929546250227 8343199357343894319375341)
                    ·
                      refine ⟨3128699759003960369765753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8343199357343894319375341 3128699759003960369765753)
                      ·
                        rfl

theorem cell23_6093121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_6093121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093121 prefixEnd_6093121 := by exact prefixLift 6093121
  have htrace : WordTrace (prefixWord ++ tailWord_6093121) baseStart_6093121 baseEnd_6093121 := by
    simpa [prefixWord, tailWord_6093121, baseEnd_6093121] using wordTrace_append hprefix tailTrace_6093121
  have hstable : (prefixWord ++ tailWord_6093121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093121).length < 2 ^ (prefixWord ++ tailWord_6093121).sum := by decide
  have hdescent : baseEnd_6093121 < baseStart_6093121 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093127 : List Nat := [1, 1, 4, 1, 2, 2, 2, 3, 1, 4, 2]
def baseStart_6093127 : Nat := 118140960795 + 6093127 * 2 ^ 59
def prefixEnd_6093127 : Nat := 4983230072969 + 3 ^ 40 * 6093127 * 2
def baseEnd_6093127 : Nat := 3128702839887887346290725

theorem tailTrace_6093127 : CollatzResearch.WordTrace tailWord_6093127 prefixEnd_6093127 3128702839887887346290725 := by
  unfold tailWord_6093127
  simp only [CollatzResearch.WordTrace]
  refine ⟨222234598996648977088461635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148156399331099318058974423 222234598996648977088461635)
  ·
    refine ⟨333351898494973465632692453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222234598996648977088461635 333351898494973465632692453)
    ·
      refine ⟨62503480967807524806129835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 333351898494973465632692453 62503480967807524806129835)
      ·
        refine ⟨93755221451711287209194753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62503480967807524806129835 93755221451711287209194753)
        ·
          refine ⟨70316416088783465406896065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93755221451711287209194753 70316416088783465406896065)
          ·
            refine ⟨52737312066587599055172049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70316416088783465406896065 52737312066587599055172049)
            ·
              refine ⟨39552984049940699291379037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52737312066587599055172049 39552984049940699291379037)
              ·
                refine ⟨14832369018727762234267139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39552984049940699291379037 14832369018727762234267139)
                ·
                  refine ⟨22248553528091643351400709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14832369018727762234267139 22248553528091643351400709)
                  ·
                    refine ⟨4171603786517183128387633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22248553528091643351400709 4171603786517183128387633)
                    ·
                      refine ⟨3128702839887887346290725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4171603786517183128387633 3128702839887887346290725)
                      ·
                        rfl

theorem cell23_6093127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 4, 2].length) (baseStart_6093127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093127 prefixEnd_6093127 := by exact prefixLift 6093127
  have htrace : WordTrace (prefixWord ++ tailWord_6093127) baseStart_6093127 baseEnd_6093127 := by
    simpa [prefixWord, tailWord_6093127, baseEnd_6093127] using wordTrace_append hprefix tailTrace_6093127
  have hstable : (prefixWord ++ tailWord_6093127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093127).length < 2 ^ (prefixWord ++ tailWord_6093127).sum := by decide
  have hdescent : baseEnd_6093127 < baseStart_6093127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093200 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 4]
def baseStart_6093200 : Nat := 118140960795 + 6093200 * 2 ^ 59
def prefixEnd_6093200 : Nat := 4983230072969 + 3 ^ 40 * 6093200 * 2
def baseEnd_6093200 : Nat := 3128740323975665560677889

theorem tailTrace_6093200 : CollatzResearch.WordTrace tailWord_6093200 prefixEnd_6093200 3128740323975665560677889 := by
  unfold tailWord_6093200
  simp only [CollatzResearch.WordTrace]
  refine ⟨111118630762692255277934527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148158174350256340370579369 111118630762692255277934527)
  ·
    refine ⟨166677946144038382916901791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111118630762692255277934527 166677946144038382916901791)
    ·
      refine ⟨250016919216057574375352687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166677946144038382916901791 250016919216057574375352687)
      ·
        refine ⟨375025378824086361563029031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250016919216057574375352687 375025378824086361563029031)
        ·
          refine ⟨562538068236129542344543547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375025378824086361563029031 562538068236129542344543547)
          ·
            refine ⟨843807102354194313516815321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 562538068236129542344543547 843807102354194313516815321)
            ·
              refine ⟨632855326765645735137611491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 843807102354194313516815321 632855326765645735137611491)
              ·
                refine ⟨949282990148468602706417237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 632855326765645735137611491 949282990148468602706417237)
                ·
                  refine ⟨11124410040802366437965827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 949282990148468602706417237 11124410040802366437965827)
                  ·
                    refine ⟨16686615061203549656948741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11124410040802366437965827 16686615061203549656948741)
                    ·
                      refine ⟨3128740323975665560677889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16686615061203549656948741 3128740323975665560677889)
                      ·
                        rfl

theorem cell23_6093200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 4].length) (baseStart_6093200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093200 prefixEnd_6093200 := by exact prefixLift 6093200
  have htrace : WordTrace (prefixWord ++ tailWord_6093200) baseStart_6093200 baseEnd_6093200 := by
    simpa [prefixWord, tailWord_6093200, baseEnd_6093200] using wordTrace_append hprefix tailTrace_6093200
  have hstable : (prefixWord ++ tailWord_6093200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093200).length < 2 ^ (prefixWord ++ tailWord_6093200).sum := by decide
  have hdescent : baseEnd_6093200 < baseStart_6093200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093220 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 2, 3, 5]
def baseStart_6093220 : Nat := 118140960795 + 6093220 * 2 ^ 59
def prefixEnd_6093220 : Nat := 4983230072969 + 3 ^ 40 * 6093220 * 2
def baseEnd_6093220 : Nat := 3128750593588755482427797

theorem tailTrace_6093220 : CollatzResearch.WordTrace tailWord_6093220 prefixEnd_6093220 3128750593588755482427797 := by
  unfold tailWord_6093220
  simp only [CollatzResearch.WordTrace]
  refine ⟨111118995492656026985798557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148158660656874702647731409 111118995492656026985798557)
  ·
    refine ⟨41669623309746010119674459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111118995492656026985798557 41669623309746010119674459)
    ·
      refine ⟨62504434964619015179511689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41669623309746010119674459 62504434964619015179511689)
      ·
        refine ⟨46878326223464261384633767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62504434964619015179511689 46878326223464261384633767)
        ·
          refine ⟨70317489335196392076950651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46878326223464261384633767 70317489335196392076950651)
          ·
            refine ⟨105476234002794588115425977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70317489335196392076950651 105476234002794588115425977)
            ·
              refine ⟨79107175502095941086569483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105476234002794588115425977 79107175502095941086569483)
              ·
                refine ⟨118660763253143911629854225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79107175502095941086569483 118660763253143911629854225)
                ·
                  refine ⟨88995572439857933722390669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118660763253143911629854225 88995572439857933722390669)
                  ·
                    refine ⟨33373339664946725145896501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88995572439857933722390669 33373339664946725145896501)
                    ·
                      refine ⟨3128750593588755482427797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33373339664946725145896501 3128750593588755482427797)
                      ·
                        rfl

theorem cell23_6093220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_6093220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093220 prefixEnd_6093220 := by exact prefixLift 6093220
  have htrace : WordTrace (prefixWord ++ tailWord_6093220) baseStart_6093220 baseEnd_6093220 := by
    simpa [prefixWord, tailWord_6093220, baseEnd_6093220] using wordTrace_append hprefix tailTrace_6093220
  have hstable : (prefixWord ++ tailWord_6093220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093220).length < 2 ^ (prefixWord ++ tailWord_6093220).sum := by decide
  have hdescent : baseEnd_6093220 < baseStart_6093220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093244 : List Nat := [2, 2, 2, 4, 1, 1, 2, 2, 3, 4]
def baseStart_6093244 : Nat := 118140960795 + 6093244 * 2 ^ 59
def prefixEnd_6093244 : Nat := 4983230072969 + 3 ^ 40 * 6093244 * 2
def baseEnd_6093244 : Nat := 1042920972374821129509229

theorem tailTrace_6093244 : CollatzResearch.WordTrace tailWord_6093244 prefixEnd_6093244 1042920972374821129509229 := by
  unfold tailWord_6093244
  simp only [CollatzResearch.WordTrace]
  refine ⟨111119433168612553035235393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148159244224816737380313857 111119433168612553035235393)
  ·
    refine ⟨83339574876459414776426545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111119433168612553035235393 83339574876459414776426545)
    ·
      refine ⟨62504681157344561082319909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83339574876459414776426545 62504681157344561082319909)
      ·
        refine ⟨11719627717002105202934983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62504681157344561082319909 11719627717002105202934983)
        ·
          refine ⟨17579441575503157804402475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11719627717002105202934983 17579441575503157804402475)
          ·
            refine ⟨26369162363254736706603713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17579441575503157804402475 26369162363254736706603713)
            ·
              refine ⟨19776871772441052529952785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26369162363254736706603713 19776871772441052529952785)
              ·
                refine ⟨14832653829330789397464589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19776871772441052529952785 14832653829330789397464589)
                ·
                  refine ⟨5562245185999046024049221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14832653829330789397464589 5562245185999046024049221)
                  ·
                    refine ⟨1042920972374821129509229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5562245185999046024049221 1042920972374821129509229)
                    ·
                      rfl

theorem cell23_6093244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 3, 4].length) (baseStart_6093244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093244 prefixEnd_6093244 := by exact prefixLift 6093244
  have htrace : WordTrace (prefixWord ++ tailWord_6093244) baseStart_6093244 baseEnd_6093244 := by
    simpa [prefixWord, tailWord_6093244, baseEnd_6093244] using wordTrace_append hprefix tailTrace_6093244
  have hstable : (prefixWord ++ tailWord_6093244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093244).length < 2 ^ (prefixWord ++ tailWord_6093244).sum := by decide
  have hdescent : baseEnd_6093244 < baseStart_6093244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093287 : List Nat := [1, 1, 5, 2, 1, 1, 2, 2, 3, 5]
def baseStart_6093287 : Nat := 118140960795 + 6093287 * 2 ^ 59
def prefixEnd_6093287 : Nat := 4983230072969 + 3 ^ 40 * 6093287 * 2
def baseEnd_6093287 : Nat := 1042928332264202240096663

theorem tailTrace_6093287 : CollatzResearch.WordTrace tailWord_6093287 prefixEnd_6093287 1042928332264202240096663 := by
  unfold tailWord_6093287
  simp only [CollatzResearch.WordTrace]
  refine ⟨222240434676069324414286115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148160289784046216276190743 222240434676069324414286115)
  ·
    refine ⟨333360652014103986621429173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222240434676069324414286115 333360652014103986621429173)
    ·
      refine ⟨31252561126322248745758985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 333360652014103986621429173 31252561126322248745758985)
      ·
        refine ⟨23439420844741686559319239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31252561126322248745758985 23439420844741686559319239)
        ·
          refine ⟨35159131267112529838978859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23439420844741686559319239 35159131267112529838978859)
          ·
            refine ⟨52738696900668794758468289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35159131267112529838978859 52738696900668794758468289)
            ·
              refine ⟨39554022675501596068851217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52738696900668794758468289 39554022675501596068851217)
              ·
                refine ⟨29665517006626197051638413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39554022675501596068851217 29665517006626197051638413)
                ·
                  refine ⟨11124568877484823894364405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29665517006626197051638413 11124568877484823894364405)
                  ·
                    refine ⟨1042928332264202240096663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11124568877484823894364405 1042928332264202240096663)
                    ·
                      rfl

theorem cell23_6093287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_6093287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093287 prefixEnd_6093287 := by exact prefixLift 6093287
  have htrace : WordTrace (prefixWord ++ tailWord_6093287) baseStart_6093287 baseEnd_6093287 := by
    simpa [prefixWord, tailWord_6093287, baseEnd_6093287] using wordTrace_append hprefix tailTrace_6093287
  have hstable : (prefixWord ++ tailWord_6093287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093287).length < 2 ^ (prefixWord ++ tailWord_6093287).sum := by decide
  have hdescent : baseEnd_6093287 < baseStart_6093287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093317 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 6, 4]
def baseStart_6093317 : Nat := 118140960795 + 6093317 * 2 ^ 59
def prefixEnd_6093317 : Nat := 4983230072969 + 3 ^ 40 * 6093317 * 2
def baseEnd_6093317 : Nat := 1042933467070747200971617

theorem tailTrace_6093317 : CollatzResearch.WordTrace tailWord_6093317 prefixEnd_6093317 1042933467070747200971617 := by
  unfold tailWord_6093317
  simp only [CollatzResearch.WordTrace]
  refine ⟨222241528865960639537878205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148161019243973759691918803 222241528865960639537878205)
  ·
    refine ⟨83340573324735239826704327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222241528865960639537878205 83340573324735239826704327)
    ·
      refine ⟨125010859987102859740056491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83340573324735239826704327 125010859987102859740056491)
      ·
        refine ⟨187516289980654289610084737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125010859987102859740056491 187516289980654289610084737)
        ·
          refine ⟨140637217485490717207563553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187516289980654289610084737 140637217485490717207563553)
          ·
            refine ⟨105477913114118037905672665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140637217485490717207563553 105477913114118037905672665)
            ·
              refine ⟨79108434835588528429254499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105477913114118037905672665 79108434835588528429254499)
              ·
                refine ⟨118662652253382792643881749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79108434835588528429254499 118662652253382792643881749)
                ·
                  refine ⟨5562311824377318405181957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 118662652253382792643881749 5562311824377318405181957)
                  ·
                    refine ⟨1042933467070747200971617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5562311824377318405181957 1042933467070747200971617)
                    ·
                      rfl

theorem cell23_6093317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 6, 4].length) (baseStart_6093317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093317 prefixEnd_6093317 := by exact prefixLift 6093317
  have htrace : WordTrace (prefixWord ++ tailWord_6093317) baseStart_6093317 baseEnd_6093317 := by
    simpa [prefixWord, tailWord_6093317, baseEnd_6093317] using wordTrace_append hprefix tailTrace_6093317
  have hstable : (prefixWord ++ tailWord_6093317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093317).length < 2 ^ (prefixWord ++ tailWord_6093317).sum := by decide
  have hdescent : baseEnd_6093317 < baseStart_6093317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093327 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 5, 2, 3]
def baseStart_6093327 : Nat := 118140960795 + 6093327 * 2 ^ 59
def prefixEnd_6093327 : Nat := 4983230072969 + 3 ^ 40 * 6093327 * 2
def baseEnd_6093327 : Nat := 3128805536018786563789805

theorem tailTrace_6093327 : CollatzResearch.WordTrace tailWord_6093327 prefixEnd_6093327 3128805536018786563789805 := by
  unfold tailWord_6093327
  simp only [CollatzResearch.WordTrace]
  refine ⟨222241893595924411245742235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148161262397282940830494823 222241893595924411245742235)
  ·
    refine ⟨333362840393886616868613353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222241893595924411245742235 333362840393886616868613353)
    ·
      refine ⟨250022130295414962651460015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333362840393886616868613353 250022130295414962651460015)
      ·
        refine ⟨375033195443122443977190023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250022130295414962651460015 375033195443122443977190023)
        ·
          refine ⟨562549793164683665965785035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375033195443122443977190023 562549793164683665965785035)
          ·
            refine ⟨843824689747025498948677553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 562549793164683665965785035 843824689747025498948677553)
            ·
              refine ⟨632868517310269124211508165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 843824689747025498948677553 632868517310269124211508165)
              ·
                refine ⟨118662846995675460789657781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 632868517310269124211508165 118662846995675460789657781)
                ·
                  refine ⟨11124641905844574449030417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 118662846995675460789657781 11124641905844574449030417)
                  ·
                    refine ⟨8343481429383430836772813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11124641905844574449030417 8343481429383430836772813)
                    ·
                      refine ⟨3128805536018786563789805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8343481429383430836772813 3128805536018786563789805)
                      ·
                        rfl

theorem cell23_6093327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 5, 2, 3].length) (baseStart_6093327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093327 prefixEnd_6093327 := by exact prefixLift 6093327
  have htrace : WordTrace (prefixWord ++ tailWord_6093327) baseStart_6093327 baseEnd_6093327 := by
    simpa [prefixWord, tailWord_6093327, baseEnd_6093327] using wordTrace_append hprefix tailTrace_6093327
  have hstable : (prefixWord ++ tailWord_6093327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093327).length < 2 ^ (prefixWord ++ tailWord_6093327).sum := by decide
  have hdescent : baseEnd_6093327 < baseStart_6093327 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093330 : List Nat := [3, 2, 18]
def baseStart_6093330 : Nat := 118140960795 + 6093330 * 2 ^ 59
def prefixEnd_6093330 : Nat := 4983230072969 + 3 ^ 40 * 6093330 * 2
def baseEnd_6093330 : Nat := 476879603179507704931

theorem tailTrace_6093330 : CollatzResearch.WordTrace tailWord_6093330 prefixEnd_6093330 476879603179507704931 := by
  unfold tailWord_6093330
  simp only [CollatzResearch.WordTrace]
  refine ⟨55560500753728385689525361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148161335343275695172067629 55560500753728385689525361)
  ·
    refine ⟨41670375565296289267144021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55560500753728385689525361 41670375565296289267144021)
    ·
      refine ⟨476879603179507704931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 18 41670375565296289267144021 476879603179507704931)
      ·
        rfl

theorem cell23_6093330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 18].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 18].length) (baseStart_6093330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093330 prefixEnd_6093330 := by exact prefixLift 6093330
  have htrace : WordTrace (prefixWord ++ tailWord_6093330) baseStart_6093330 baseEnd_6093330 := by
    simpa [prefixWord, tailWord_6093330, baseEnd_6093330] using wordTrace_append hprefix tailTrace_6093330
  have hstable : (prefixWord ++ tailWord_6093330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093330).length < 2 ^ (prefixWord ++ tailWord_6093330).sum := by decide
  have hdescent : baseEnd_6093330 < baseStart_6093330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093335 : List Nat := [1, 1, 3, 6, 1, 1, 1, 4, 1, 1, 3]
def baseStart_6093335 : Nat := 118140960795 + 6093335 * 2 ^ 59
def prefixEnd_6093335 : Nat := 4983230072969 + 3 ^ 40 * 6093335 * 2
def baseEnd_6093335 : Nat := 3128809643864022532489769

theorem tailTrace_6093335 : CollatzResearch.WordTrace tailWord_6093335 prefixEnd_6093335 3128809643864022532489769 := by
  unfold tailWord_6093335
  simp only [CollatzResearch.WordTrace]
  refine ⟨222242185379895428612033459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148161456919930285741355639 222242185379895428612033459)
  ·
    refine ⟨333363278069843142918050189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222242185379895428612033459 333363278069843142918050189)
    ·
      refine ⟨125011229276191178594268821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 333363278069843142918050189 125011229276191178594268821)
      ·
        refine ⟨5859901372321461496606351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 125011229276191178594268821 5859901372321461496606351)
        ·
          refine ⟨8789852058482192244909527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5859901372321461496606351 8789852058482192244909527)
          ·
            refine ⟨13184778087723288367364291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8789852058482192244909527 13184778087723288367364291)
            ·
              refine ⟨19777167131584932551046437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13184778087723288367364291 19777167131584932551046437)
              ·
                refine ⟨3708218837172174853321207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19777167131584932551046437 3708218837172174853321207)
                ·
                  refine ⟨5562328255758262279981811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3708218837172174853321207 5562328255758262279981811)
                  ·
                    refine ⟨8343492383637393419972717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5562328255758262279981811 8343492383637393419972717)
                    ·
                      refine ⟨3128809643864022532489769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8343492383637393419972717 3128809643864022532489769)
                      ·
                        rfl

theorem cell23_6093335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_6093335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093335 prefixEnd_6093335 := by exact prefixLift 6093335
  have htrace : WordTrace (prefixWord ++ tailWord_6093335) baseStart_6093335 baseEnd_6093335 := by
    simpa [prefixWord, tailWord_6093335, baseEnd_6093335] using wordTrace_append hprefix tailTrace_6093335
  have hstable : (prefixWord ++ tailWord_6093335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093335).length < 2 ^ (prefixWord ++ tailWord_6093335).sum := by decide
  have hdescent : baseEnd_6093335 < baseStart_6093335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093347 : List Nat := [1, 1, 1, 4, 4, 1, 3, 8]
def baseStart_6093347 : Nat := 118140960795 + 6093347 * 2 ^ 59
def prefixEnd_6093347 : Nat := 4983230072969 + 3 ^ 40 * 6093347 * 2
def baseEnd_6093347 : Nat := 115882066875254684649619

theorem tailTrace_6093347 : CollatzResearch.WordTrace tailWord_6093347 prefixEnd_6093347 115882066875254684649619 := by
  unfold tailWord_6093347
  simp only [CollatzResearch.WordTrace]
  refine ⟨222242623055851954661470295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148161748703901303107646863 222242623055851954661470295)
  ·
    refine ⟨333363934583777931992205443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222242623055851954661470295 333363934583777931992205443)
    ·
      refine ⟨500045901875666897988308165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333363934583777931992205443 500045901875666897988308165)
      ·
        refine ⟨93758606601687543372807781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 500045901875666897988308165 93758606601687543372807781)
        ·
          refine ⟨17579738737816414382401459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93758606601687543372807781 17579738737816414382401459)
          ·
            refine ⟨26369608106724621573602189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17579738737816414382401459 26369608106724621573602189)
            ·
              refine ⟨9888603040021733090100821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26369608106724621573602189 9888603040021733090100821)
              ·
                refine ⟨115882066875254684649619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9888603040021733090100821 115882066875254684649619)
                ·
                  rfl

theorem cell23_6093347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 8].length) (baseStart_6093347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093347 prefixEnd_6093347 := by exact prefixLift 6093347
  have htrace : WordTrace (prefixWord ++ tailWord_6093347) baseStart_6093347 baseEnd_6093347 := by
    simpa [prefixWord, tailWord_6093347, baseEnd_6093347] using wordTrace_append hprefix tailTrace_6093347
  have hstable : (prefixWord ++ tailWord_6093347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093347).length < 2 ^ (prefixWord ++ tailWord_6093347).sum := by decide
  have hdescent : baseEnd_6093347 < baseStart_6093347 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093354 : List Nat := [3, 1, 4, 1, 1, 2, 1, 3, 1, 2, 4]
def baseStart_6093354 : Nat := 118140960795 + 6093354 * 2 ^ 59
def prefixEnd_6093354 : Nat := 4983230072969 + 3 ^ 40 * 6093354 * 2
def baseEnd_6093354 : Nat := 3128819399996457958152181

theorem tailTrace_6093354 : CollatzResearch.WordTrace tailWord_6093354 prefixEnd_6093354 3128819399996457958152181 := by
  unfold tailWord_6093354
  simp only [CollatzResearch.WordTrace]
  refine ⟨55560719591706648714243779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148161918911217729904650077 55560719591706648714243779)
  ·
    refine ⟨83341079387559973071365669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55560719591706648714243779 83341079387559973071365669)
    ·
      refine ⟨15626452385167494950881063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83341079387559973071365669 15626452385167494950881063)
      ·
        refine ⟨23439678577751242426321595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15626452385167494950881063 23439678577751242426321595)
        ·
          refine ⟨35159517866626863639482393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23439678577751242426321595 35159517866626863639482393)
          ·
            refine ⟨26369638399970147729611795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35159517866626863639482393 26369638399970147729611795)
            ·
              refine ⟨39554457599955221594417693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26369638399970147729611795 39554457599955221594417693)
              ·
                refine ⟨14832921599983208097906635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39554457599955221594417693 14832921599983208097906635)
                ·
                  refine ⟨22249382399974812146859953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14832921599983208097906635 22249382399974812146859953)
                  ·
                    refine ⟨16687036799981109110144965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22249382399974812146859953 16687036799981109110144965)
                    ·
                      refine ⟨3128819399996457958152181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16687036799981109110144965 3128819399996457958152181)
                      ·
                        rfl

theorem cell23_6093354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_6093354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093354 prefixEnd_6093354 := by exact prefixLift 6093354
  have htrace : WordTrace (prefixWord ++ tailWord_6093354) baseStart_6093354 baseEnd_6093354 := by
    simpa [prefixWord, tailWord_6093354, baseEnd_6093354] using wordTrace_append hprefix tailTrace_6093354
  have hstable : (prefixWord ++ tailWord_6093354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093354).length < 2 ^ (prefixWord ++ tailWord_6093354).sum := by decide
  have hdescent : baseEnd_6093354 < baseStart_6093354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093391 : List Nat := [1, 1, 2, 1, 1, 2, 7, 2, 2, 1, 3]
def baseStart_6093391 : Nat := 118140960795 + 6093391 * 2 ^ 59
def prefixEnd_6093391 : Nat := 4983230072969 + 3 ^ 40 * 6093391 * 2
def baseEnd_6093391 : Nat := 3128838398780674313389511

theorem tailTrace_6093391 : CollatzResearch.WordTrace tailWord_6093391 prefixEnd_6093391 3128838398780674313389511 := by
  unfold tailWord_6093391
  simp only [CollatzResearch.WordTrace]
  refine ⟨222244227867692550176072027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148162818578461700117381351 222244227867692550176072027)
  ·
    refine ⟨333366341801538825264108041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222244227867692550176072027 333366341801538825264108041)
    ·
      refine ⟨250024756351154118948081031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333366341801538825264108041 250024756351154118948081031)
      ·
        refine ⟨375037134526731178422121547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250024756351154118948081031 375037134526731178422121547)
        ·
          refine ⟨562555701790096767633182321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375037134526731178422121547 562555701790096767633182321)
          ·
            refine ⟨421916776342572575724886741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 562555701790096767633182321 421916776342572575724886741)
            ·
              refine ⟨9888674445529044743552033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 421916776342572575724886741 9888674445529044743552033)
              ·
                refine ⟨7416505834146783557664025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9888674445529044743552033 7416505834146783557664025)
                ·
                  refine ⟨5562379375610087668248019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7416505834146783557664025 5562379375610087668248019)
                  ·
                    refine ⟨8343569063415131502372029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5562379375610087668248019 8343569063415131502372029)
                    ·
                      refine ⟨3128838398780674313389511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8343569063415131502372029 3128838398780674313389511)
                      ·
                        rfl

theorem cell23_6093391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 2, 2, 1, 3].length) (baseStart_6093391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093391 prefixEnd_6093391 := by exact prefixLift 6093391
  have htrace : WordTrace (prefixWord ++ tailWord_6093391) baseStart_6093391 baseEnd_6093391 := by
    simpa [prefixWord, tailWord_6093391, baseEnd_6093391] using wordTrace_append hprefix tailTrace_6093391
  have hstable : (prefixWord ++ tailWord_6093391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093391).length < 2 ^ (prefixWord ++ tailWord_6093391).sum := by decide
  have hdescent : baseEnd_6093391 < baseStart_6093391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093397 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 1, 5, 4]
def baseStart_6093397 : Nat := 118140960795 + 6093397 * 2 ^ 59
def prefixEnd_6093397 : Nat := 4983230072969 + 3 ^ 40 * 6093397 * 2
def baseEnd_6093397 : Nat := 3128841479664601289914483

theorem tailTrace_6093397 : CollatzResearch.WordTrace tailWord_6093397 prefixEnd_6093397 3128841479664601289914483 := by
  unfold tailWord_6093397
  simp only [CollatzResearch.WordTrace]
  refine ⟨222244446705670813200790445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148162964470447208800526963 222244446705670813200790445)
  ·
    refine ⟨83341667514626554950296417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222244446705670813200790445 83341667514626554950296417)
    ·
      refine ⟨62506250635969916212722313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83341667514626554950296417 62506250635969916212722313)
      ·
        refine ⟨46879687976977437159541735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62506250635969916212722313 46879687976977437159541735)
        ·
          refine ⟨70319531965466155739312603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46879687976977437159541735 70319531965466155739312603)
          ·
            refine ⟨105479297948199233608968905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70319531965466155739312603 105479297948199233608968905)
            ·
              refine ⟨79109473461149425206726679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105479297948199233608968905 79109473461149425206726679)
              ·
                refine ⟨118664210191724137810090019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79109473461149425206726679 118664210191724137810090019)
                ·
                  refine ⟨177996315287586206715135029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118664210191724137810090019 177996315287586206715135029)
                  ·
                    refine ⟨16687154558211206879543909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 177996315287586206715135029 16687154558211206879543909)
                    ·
                      refine ⟨3128841479664601289914483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16687154558211206879543909 3128841479664601289914483)
                      ·
                        rfl

theorem cell23_6093397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_6093397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093397 prefixEnd_6093397 := by exact prefixLift 6093397
  have htrace : WordTrace (prefixWord ++ tailWord_6093397) baseStart_6093397 baseEnd_6093397 := by
    simpa [prefixWord, tailWord_6093397, baseEnd_6093397] using wordTrace_append hprefix tailTrace_6093397
  have hstable : (prefixWord ++ tailWord_6093397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093397).length < 2 ^ (prefixWord ++ tailWord_6093397).sum := by decide
  have hdescent : baseEnd_6093397 < baseStart_6093397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093417 : List Nat := [1, 2, 1, 1, 1, 4, 1, 4, 2, 1, 5]
def baseStart_6093417 : Nat := 118140960795 + 6093417 * 2 ^ 59
def prefixEnd_6093417 : Nat := 4983230072969 + 3 ^ 40 * 6093417 * 2
def baseEnd_6093417 : Nat := 3128851749277691211664391

theorem tailTrace_6093417 : CollatzResearch.WordTrace tailWord_6093417 prefixEnd_6093417 3128851749277691211664391 := by
  unfold tailWord_6093417
  simp only [CollatzResearch.WordTrace]
  refine ⟨222245176165598356616518505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148163450777065571077679003 222245176165598356616518505)
  ·
    refine ⟨166683882124198767462388879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222245176165598356616518505 166683882124198767462388879)
    ·
      refine ⟨250025823186298151193583319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166683882124198767462388879 250025823186298151193583319)
      ·
        refine ⟨375038734779447226790374979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250025823186298151193583319 375038734779447226790374979)
        ·
          refine ⟨562558102169170840185562469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375038734779447226790374979 562558102169170840185562469)
          ·
            refine ⟨105479644156719532534792963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 562558102169170840185562469 105479644156719532534792963)
            ·
              refine ⟨158219466235079298802189445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105479644156719532534792963 158219466235079298802189445)
              ·
                refine ⟨29666149919077368525410521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 158219466235079298802189445 29666149919077368525410521)
                ·
                  refine ⟨22249612439308026394057891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29666149919077368525410521 22249612439308026394057891)
                  ·
                    refine ⟨33374418658962039591086837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22249612439308026394057891 33374418658962039591086837)
                    ·
                      refine ⟨3128851749277691211664391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33374418658962039591086837 3128851749277691211664391)
                      ·
                        rfl

theorem cell23_6093417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 1, 5].length) (baseStart_6093417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093417 prefixEnd_6093417 := by exact prefixLift 6093417
  have htrace : WordTrace (prefixWord ++ tailWord_6093417) baseStart_6093417 baseEnd_6093417 := by
    simpa [prefixWord, tailWord_6093417, baseEnd_6093417] using wordTrace_append hprefix tailTrace_6093417
  have hstable : (prefixWord ++ tailWord_6093417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093417).length < 2 ^ (prefixWord ++ tailWord_6093417).sum := by decide
  have hdescent : baseEnd_6093417 < baseStart_6093417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093418 : List Nat := [3, 1, 3, 2, 1, 1, 4, 2, 1, 3, 2]
def baseStart_6093418 : Nat := 118140960795 + 6093418 * 2 ^ 59
def prefixEnd_6093418 : Nat := 4983230072969 + 3 ^ 40 * 6093418 * 2
def baseEnd_6093418 : Nat := 3128852262758345707751887

theorem tailTrace_6093418 : CollatzResearch.WordTrace tailWord_6093418 prefixEnd_6093418 3128852262758345707751887 := by
  unfold tailWord_6093418
  simp only [CollatzResearch.WordTrace]
  refine ⟨55561303159648683446826227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148163475092396489191536605 55561303159648683446826227)
  ·
    refine ⟨83341954739473025170239341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55561303159648683446826227 83341954739473025170239341)
    ·
      refine ⟨31253233027302384438839753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83341954739473025170239341 31253233027302384438839753)
      ·
        refine ⟨23439924770476788329129815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31253233027302384438839753 23439924770476788329129815)
        ·
          refine ⟨35159887155715182493694723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23439924770476788329129815 35159887155715182493694723)
          ·
            refine ⟨52739830733572773740542085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35159887155715182493694723 52739830733572773740542085)
            ·
              refine ⟨9888718262544895076351641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52739830733572773740542085 9888718262544895076351641)
              ·
                refine ⟨7416538696908671307263731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9888718262544895076351641 7416538696908671307263731)
                ·
                  refine ⟨11124808045363006960895597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7416538696908671307263731 11124808045363006960895597)
                  ·
                    refine ⟨4171803017011127610335849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11124808045363006960895597 4171803017011127610335849)
                    ·
                      refine ⟨3128852262758345707751887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4171803017011127610335849 3128852262758345707751887)
                      ·
                        rfl

theorem cell23_6093418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_6093418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093418 prefixEnd_6093418 := by exact prefixLift 6093418
  have htrace : WordTrace (prefixWord ++ tailWord_6093418) baseStart_6093418 baseEnd_6093418 := by
    simpa [prefixWord, tailWord_6093418, baseEnd_6093418] using wordTrace_append hprefix tailTrace_6093418
  have hstable : (prefixWord ++ tailWord_6093418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093418).length < 2 ^ (prefixWord ++ tailWord_6093418).sum := by decide
  have hdescent : baseEnd_6093418 < baseStart_6093418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093427 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 4, 2, 4]
def baseStart_6093427 : Nat := 118140960795 + 6093427 * 2 ^ 59
def prefixEnd_6093427 : Nat := 4983230072969 + 3 ^ 40 * 6093427 * 2
def baseEnd_6093427 : Nat := 3128856884084236172539345

theorem tailTrace_6093427 : CollatzResearch.WordTrace tailWord_6093427 prefixEnd_6093427 3128856884084236172539345 := by
  unfold tailWord_6093427
  simp only [CollatzResearch.WordTrace]
  refine ⟨222245540895562128324382535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148163693930374752216255023 222245540895562128324382535)
  ·
    refine ⟨333368311343343192486573803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222245540895562128324382535 333368311343343192486573803)
    ·
      refine ⟨500052467015014788729860705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333368311343343192486573803 500052467015014788729860705)
      ·
        refine ⟨375039350261261091547395529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 500052467015014788729860705 375039350261261091547395529)
        ·
          refine ⟨281279512695945818660546647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 375039350261261091547395529 281279512695945818660546647)
          ·
            refine ⟨421919269043918727990819971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281279512695945818660546647 421919269043918727990819971)
            ·
              refine ⟨632878903565878091986229957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 421919269043918727990819971 632878903565878091986229957)
              ·
                refine ⟨118664794418602142247418117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 632878903565878091986229957 118664794418602142247418117)
                ·
                  refine ⟨22249648953487901671390897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 118664794418602142247418117 22249648953487901671390897)
                  ·
                    refine ⟨16687236715115926253543173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22249648953487901671390897 16687236715115926253543173)
                    ·
                      refine ⟨3128856884084236172539345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16687236715115926253543173 3128856884084236172539345)
                      ·
                        rfl

theorem cell23_6093427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 2, 4].length) (baseStart_6093427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093427 prefixEnd_6093427 := by exact prefixLift 6093427
  have htrace : WordTrace (prefixWord ++ tailWord_6093427) baseStart_6093427 baseEnd_6093427 := by
    simpa [prefixWord, tailWord_6093427, baseEnd_6093427] using wordTrace_append hprefix tailTrace_6093427
  have hstable : (prefixWord ++ tailWord_6093427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093427).length < 2 ^ (prefixWord ++ tailWord_6093427).sum := by decide
  have hdescent : baseEnd_6093427 < baseStart_6093427 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093431 : List Nat := [1, 1, 3, 1, 1, 3, 3, 2, 4, 2, 2]
def baseStart_6093431 : Nat := 118140960795 + 6093431 * 2 ^ 59
def prefixEnd_6093431 : Nat := 4983230072969 + 3 ^ 40 * 6093431 * 2
def baseEnd_6093431 : Nat := 3128858938006854156889327

theorem tailTrace_6093431 : CollatzResearch.WordTrace tailWord_6093431 prefixEnd_6093431 3128858938006854156889327 := by
  unfold tailWord_6093431
  simp only [CollatzResearch.WordTrace]
  refine ⟨222245686787547637007528147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148163791191698424671685431 222245686787547637007528147)
  ·
    refine ⟨333368530181321455511292221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222245686787547637007528147 333368530181321455511292221)
    ·
      refine ⟨125013198817995545816734583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 333368530181321455511292221 125013198817995545816734583)
      ·
        refine ⟨187519798226993318725101875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125013198817995545816734583 187519798226993318725101875)
        ·
          refine ⟨281279697340489978087652813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187519798226993318725101875 281279697340489978087652813)
          ·
            refine ⟨105479886502683741782869805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 281279697340489978087652813 105479886502683741782869805)
            ·
              refine ⟨39554957438506403168576177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105479886502683741782869805 39554957438506403168576177)
              ·
                refine ⟨29666218078879802376432133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39554957438506403168576177 29666218078879802376432133)
                ·
                  refine ⟨5562415889789962945581025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29666218078879802376432133 5562415889789962945581025)
                  ·
                    refine ⟨4171811917342472209185769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5562415889789962945581025 4171811917342472209185769)
                    ·
                      refine ⟨3128858938006854156889327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4171811917342472209185769 3128858938006854156889327)
                      ·
                        rfl

theorem cell23_6093431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 4, 2, 2].length) (baseStart_6093431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093431 prefixEnd_6093431 := by exact prefixLift 6093431
  have htrace : WordTrace (prefixWord ++ tailWord_6093431) baseStart_6093431 baseEnd_6093431 := by
    simpa [prefixWord, tailWord_6093431, baseEnd_6093431] using wordTrace_append hprefix tailTrace_6093431
  have hstable : (prefixWord ++ tailWord_6093431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093431).length < 2 ^ (prefixWord ++ tailWord_6093431).sum := by decide
  have hdescent : baseEnd_6093431 < baseStart_6093431 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093447 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 7]
def baseStart_6093447 : Nat := 118140960795 + 6093447 * 2 ^ 59
def prefixEnd_6093447 : Nat := 4983230072969 + 3 ^ 40 * 6093447 * 2
def baseEnd_6093447 : Nat := 3128867153697326094289253

theorem tailTrace_6093447 : CollatzResearch.WordTrace tailWord_6093447 prefixEnd_6093447 3128867153697326094289253 := by
  unfold tailWord_6093447
  simp only [CollatzResearch.WordTrace]
  refine ⟨222246270355489671740110595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148164180236993114493407063 222246270355489671740110595)
  ·
    refine ⟨333369405533234507610165893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222246270355489671740110595 333369405533234507610165893)
    ·
      refine ⟨62506763537481470176906105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 333369405533234507610165893 62506763537481470176906105)
      ·
        refine ⟨46880072653111102632679579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62506763537481470176906105 46880072653111102632679579)
        ·
          refine ⟨70320108979666653949019369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46880072653111102632679579 70320108979666653949019369)
          ·
            refine ⟨52740081734749990461764527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70320108979666653949019369 52740081734749990461764527)
            ·
              refine ⟨79110122602124985692646791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52740081734749990461764527 79110122602124985692646791)
              ·
                refine ⟨118665183903187478538970187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79110122602124985692646791 118665183903187478538970187)
                ·
                  refine ⟨177997775854781217808455281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118665183903187478538970187 177997775854781217808455281)
                  ·
                    refine ⟨133498331891085913356341461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 177997775854781217808455281 133498331891085913356341461)
                    ·
                      refine ⟨3128867153697326094289253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 133498331891085913356341461 3128867153697326094289253)
                      ·
                        rfl

theorem cell23_6093447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_6093447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093447 prefixEnd_6093447 := by exact prefixLift 6093447
  have htrace : WordTrace (prefixWord ++ tailWord_6093447) baseStart_6093447 baseEnd_6093447 := by
    simpa [prefixWord, tailWord_6093447, baseEnd_6093447] using wordTrace_append hprefix tailTrace_6093447
  have hstable : (prefixWord ++ tailWord_6093447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093447).length < 2 ^ (prefixWord ++ tailWord_6093447).sum := by decide
  have hdescent : baseEnd_6093447 < baseStart_6093447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093464 : List Nat := [2, 1, 2, 4, 1, 1, 2, 1, 1, 5, 3]
def baseStart_6093464 : Nat := 118140960795 + 6093464 * 2 ^ 59
def prefixEnd_6093464 : Nat := 4983230072969 + 3 ^ 40 * 6093464 * 2
def baseEnd_6093464 : Nat := 3128875882868452527776675

theorem tailTrace_6093464 : CollatzResearch.WordTrace tailWord_6093464 prefixEnd_6093464 3128875882868452527776675 := by
  unfold tailWord_6093464
  simp only [CollatzResearch.WordTrace]
  refine ⟨111123445198214041821739723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148164593597618722428986297 111123445198214041821739723)
  ·
    refine ⟨166685167797321062732609585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111123445198214041821739723 166685167797321062732609585)
    ·
      refine ⟨125013875847990797049457189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166685167797321062732609585 125013875847990797049457189)
      ·
        refine ⟨23440101721498274446773223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125013875847990797049457189 23440101721498274446773223)
        ·
          refine ⟨35160152582247411670159835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23440101721498274446773223 35160152582247411670159835)
          ·
            refine ⟨52740228873371117505239753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35160152582247411670159835 52740228873371117505239753)
            ·
              refine ⟨39555171655028338128929815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52740228873371117505239753 39555171655028338128929815)
              ·
                refine ⟨59332757482542507193394723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39555171655028338128929815 59332757482542507193394723)
                ·
                  refine ⟨88999136223813760790092085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59332757482542507193394723 88999136223813760790092085)
                  ·
                    refine ⟨8343669020982540074071133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 88999136223813760790092085 8343669020982540074071133)
                    ·
                      refine ⟨3128875882868452527776675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8343669020982540074071133 3128875882868452527776675)
                      ·
                        rfl

theorem cell23_6093464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_6093464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093464 prefixEnd_6093464 := by exact prefixLift 6093464
  have htrace : WordTrace (prefixWord ++ tailWord_6093464) baseStart_6093464 baseEnd_6093464 := by
    simpa [prefixWord, tailWord_6093464, baseEnd_6093464] using wordTrace_append hprefix tailTrace_6093464
  have hstable : (prefixWord ++ tailWord_6093464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093464).length < 2 ^ (prefixWord ++ tailWord_6093464).sum := by decide
  have hdescent : baseEnd_6093464 < baseStart_6093464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093477 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 3, 1, 7]
def baseStart_6093477 : Nat := 118140960795 + 6093477 * 2 ^ 59
def prefixEnd_6093477 : Nat := 4983230072969 + 3 ^ 40 * 6093477 * 2
def baseEnd_6093477 : Nat := 3128882558116960976914115

theorem tailTrace_6093477 : CollatzResearch.WordTrace tailWord_6093477 prefixEnd_6093477 3128882558116960976914115 := by
  unfold tailWord_6093477
  simp only [CollatzResearch.WordTrace]
  refine ⟨222247364545380986863702685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148164909696920657909135123 222247364545380986863702685)
  ·
    refine ⟨83342761704517870073888507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222247364545380986863702685 83342761704517870073888507)
    ·
      refine ⟨125014142556776805110832761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83342761704517870073888507 125014142556776805110832761)
      ·
        refine ⟨93760606917582603833124571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125014142556776805110832761 93760606917582603833124571)
        ·
          refine ⟨140640910376373905749686857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93760606917582603833124571 140640910376373905749686857)
          ·
            refine ⟨105480682782280429312265143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140640910376373905749686857 105480682782280429312265143)
            ·
              refine ⟨158221024173420643968397715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105480682782280429312265143 158221024173420643968397715)
              ·
                refine ⟨237331536260130965952596573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158221024173420643968397715 237331536260130965952596573)
                ·
                  refine ⟨88999326097549112232223715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 237331536260130965952596573 88999326097549112232223715)
                  ·
                    refine ⟨133498989146323668348335573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 88999326097549112232223715 133498989146323668348335573)
                    ·
                      refine ⟨3128882558116960976914115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 133498989146323668348335573 3128882558116960976914115)
                      ·
                        rfl

theorem cell23_6093477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_6093477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093477 prefixEnd_6093477 := by exact prefixLift 6093477
  have htrace : WordTrace (prefixWord ++ tailWord_6093477) baseStart_6093477 baseEnd_6093477 := by
    simpa [prefixWord, tailWord_6093477, baseEnd_6093477] using wordTrace_append hprefix tailTrace_6093477
  have hstable : (prefixWord ++ tailWord_6093477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093477).length < 2 ^ (prefixWord ++ tailWord_6093477).sum := by decide
  have hdescent : baseEnd_6093477 < baseStart_6093477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093505 : List Nat := [1, 2, 6, 2, 1, 1, 1, 4, 5]
def baseStart_6093505 : Nat := 118140960795 + 6093505 * 2 ^ 59
def prefixEnd_6093505 : Nat := 4983230072969 + 3 ^ 40 * 6093505 * 2
def baseEnd_6093505 : Nat := 347655215063920763040443

theorem tailTrace_6093505 : CollatzResearch.WordTrace tailWord_6093505 prefixEnd_6093505 347655215063920763040443 := by
  unfold tailWord_6093505
  simp only [CollatzResearch.WordTrace]
  refine ⟨222248385789279547645721969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148165590526186365097147979 222248385789279547645721969)
  ·
    refine ⟨166686289341959660734291477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222248385789279547645721969 166686289341959660734291477)
    ·
      refine ⟨7813419812904359096919913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 166686289341959660734291477 7813419812904359096919913)
      ·
        refine ⟨5860064859678269322689935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7813419812904359096919913 5860064859678269322689935)
        ·
          refine ⟨8790097289517403984034903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5860064859678269322689935 8790097289517403984034903)
          ·
            refine ⟨13185145934276105976052355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8790097289517403984034903 13185145934276105976052355)
            ·
              refine ⟨19777718901414158964078533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13185145934276105976052355 19777718901414158964078533)
              ·
                refine ⟨3708322294015154805764725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19777718901414158964078533 3708322294015154805764725)
                ·
                  refine ⟨347655215063920763040443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3708322294015154805764725 347655215063920763040443)
                  ·
                    rfl

theorem cell23_6093505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 4, 5].length) (baseStart_6093505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093505 prefixEnd_6093505 := by exact prefixLift 6093505
  have htrace : WordTrace (prefixWord ++ tailWord_6093505) baseStart_6093505 baseEnd_6093505 := by
    simpa [prefixWord, tailWord_6093505, baseEnd_6093505] using wordTrace_append hprefix tailTrace_6093505
  have hstable : (prefixWord ++ tailWord_6093505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093505).length < 2 ^ (prefixWord ++ tailWord_6093505).sum := by decide
  have hdescent : baseEnd_6093505 < baseStart_6093505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093521 : List Nat := [1, 2, 2, 1, 2, 3, 3, 1, 2, 4, 2]
def baseStart_6093521 : Nat := 118140960795 + 6093521 * 2 ^ 59
def prefixEnd_6093521 : Nat := 4983230072969 + 3 ^ 40 * 6093521 * 2
def baseEnd_6093521 : Nat := 3128905151265758804763913

theorem tailTrace_6093521 : CollatzResearch.WordTrace tailWord_6093521 prefixEnd_6093521 3128905151265758804763913 := by
  unfold tailWord_6093521
  simp only [CollatzResearch.WordTrace]
  refine ⟨222248969357221582378304417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148165979571481054918869611 222248969357221582378304417)
  ·
    refine ⟨166686727017916186783728313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222248969357221582378304417 166686727017916186783728313)
    ·
      refine ⟨125015045263437140087796235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166686727017916186783728313 125015045263437140087796235)
      ·
        refine ⟨187522567895155710131694353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125015045263437140087796235 187522567895155710131694353)
        ·
          refine ⟨140641925921366782598770765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187522567895155710131694353 140641925921366782598770765)
          ·
            refine ⟨52740722220512543474539037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140641925921366782598770765 52740722220512543474539037)
            ·
              refine ⟨19777770832692203802952139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52740722220512543474539037 19777770832692203802952139)
              ·
                refine ⟨29666656249038305704428209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19777770832692203802952139 29666656249038305704428209)
                ·
                  refine ⟨22249992186778729278321157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29666656249038305704428209 22249992186778729278321157)
                  ·
                    refine ⟨4171873535021011739685217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22249992186778729278321157 4171873535021011739685217)
                    ·
                      refine ⟨3128905151265758804763913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4171873535021011739685217 3128905151265758804763913)
                      ·
                        rfl

theorem cell23_6093521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 4, 2].length) (baseStart_6093521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093521 prefixEnd_6093521 := by exact prefixLift 6093521
  have htrace : WordTrace (prefixWord ++ tailWord_6093521) baseStart_6093521 baseEnd_6093521 := by
    simpa [prefixWord, tailWord_6093521, baseEnd_6093521] using wordTrace_append hprefix tailTrace_6093521
  have hstable : (prefixWord ++ tailWord_6093521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093521).length < 2 ^ (prefixWord ++ tailWord_6093521).sum := by decide
  have hdescent : baseEnd_6093521 < baseStart_6093521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093541 : List Nat := [1, 3, 1, 4, 1, 3, 1, 1, 1, 4, 3]
def baseStart_6093541 : Nat := 118140960795 + 6093541 * 2 ^ 59
def prefixEnd_6093541 : Nat := 4983230072969 + 3 ^ 40 * 6093541 * 2
def baseEnd_6093541 : Nat := 3128915420878848726513821

theorem tailTrace_6093541 : CollatzResearch.WordTrace tailWord_6093541 prefixEnd_6093541 3128915420878848726513821 := by
  unfold tailWord_6093541
  simp only [CollatzResearch.WordTrace]
  refine ⟨222249698817149125794032477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148166465878099417196021651 222249698817149125794032477)
  ·
    refine ⟨83343637056430922172762179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222249698817149125794032477 83343637056430922172762179)
    ·
      refine ⟨125015455584646383259143269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83343637056430922172762179 125015455584646383259143269)
      ·
        refine ⟨23440397922121196861089363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125015455584646383259143269 23440397922121196861089363)
        ·
          refine ⟨35160596883181795291634045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23440397922121196861089363 35160596883181795291634045)
          ·
            refine ⟨13185223831193173234362767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35160596883181795291634045 13185223831193173234362767)
            ·
              refine ⟨19777835746789759851544151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13185223831193173234362767 19777835746789759851544151)
              ·
                refine ⟨29666753620184639777316227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19777835746789759851544151 29666753620184639777316227)
                ·
                  refine ⟨44500130430276959665974341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29666753620184639777316227 44500130430276959665974341)
                  ·
                    refine ⟨8343774455676929937370189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44500130430276959665974341 8343774455676929937370189)
                    ·
                      refine ⟨3128915420878848726513821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8343774455676929937370189 3128915420878848726513821)
                      ·
                        rfl

theorem cell23_6093541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_6093541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093541 prefixEnd_6093541 := by exact prefixLift 6093541
  have htrace : WordTrace (prefixWord ++ tailWord_6093541) baseStart_6093541 baseEnd_6093541 := by
    simpa [prefixWord, tailWord_6093541, baseEnd_6093541] using wordTrace_append hprefix tailTrace_6093541
  have hstable : (prefixWord ++ tailWord_6093541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093541).length < 2 ^ (prefixWord ++ tailWord_6093541).sum := by decide
  have hdescent : baseEnd_6093541 < baseStart_6093541 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093564 : List Nat := [2, 2, 2, 1, 3, 2, 1, 1, 1, 2, 6]
def baseStart_6093564 : Nat := 118140960795 + 6093564 * 2 ^ 59
def prefixEnd_6093564 : Nat := 4983230072969 + 3 ^ 40 * 6093564 * 2
def baseEnd_6093564 : Nat := 3128927230933902136526215

theorem tailTrace_6093564 : CollatzResearch.WordTrace tailWord_6093564 prefixEnd_6093564 3128927230933902136526215 := by
  unfold tailWord_6093564
  simp only [CollatzResearch.WordTrace]
  refine ⟨111125268848032900361059873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148167025130710533814746497 111125268848032900361059873)
  ·
    refine ⟨83343951636024675270794905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111125268848032900361059873 83343951636024675270794905)
    ·
      refine ⟨62507963727018506453096179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83343951636024675270794905 62507963727018506453096179)
      ·
        refine ⟨93761945590527759679644269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62507963727018506453096179 93761945590527759679644269)
        ·
          refine ⟨35160729596447909879866601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93761945590527759679644269 35160729596447909879866601)
          ·
            refine ⟨26370547197335932409899951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35160729596447909879866601 26370547197335932409899951)
            ·
              refine ⟨39555820796003898614849927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26370547197335932409899951 39555820796003898614849927)
              ·
                refine ⟨59333731194005847922274891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39555820796003898614849927 59333731194005847922274891)
                ·
                  refine ⟨89000596791008771883412337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59333731194005847922274891 89000596791008771883412337)
                  ·
                    refine ⟨66750447593256578912559253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 89000596791008771883412337 66750447593256578912559253)
                    ·
                      refine ⟨3128927230933902136526215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66750447593256578912559253 3128927230933902136526215)
                      ·
                        rfl

theorem cell23_6093564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_6093564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093564 prefixEnd_6093564 := by exact prefixLift 6093564
  have htrace : WordTrace (prefixWord ++ tailWord_6093564) baseStart_6093564 baseEnd_6093564 := by
    simpa [prefixWord, tailWord_6093564, baseEnd_6093564] using wordTrace_append hprefix tailTrace_6093564
  have hstable : (prefixWord ++ tailWord_6093564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093564).length < 2 ^ (prefixWord ++ tailWord_6093564).sum := by decide
  have hdescent : baseEnd_6093564 < baseStart_6093564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093624 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 3, 1, 6]
def baseStart_6093624 : Nat := 118140960795 + 6093624 * 2 ^ 59
def prefixEnd_6093624 : Nat := 4983230072969 + 3 ^ 40 * 6093624 * 2
def baseEnd_6093624 : Nat := 3128958039773171901775939

theorem tailTrace_6093624 : CollatzResearch.WordTrace tailWord_6093624 prefixEnd_6093624 3128958039773171901775939 := by
  unfold tailWord_6093624
  simp only [CollatzResearch.WordTrace]
  refine ⟨111126363037924215484651963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148168484050565620646202617 111126363037924215484651963)
  ·
    refine ⟨166689544556886323226977945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111126363037924215484651963 166689544556886323226977945)
    ·
      refine ⟨125017158417664742420233459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166689544556886323226977945 125017158417664742420233459)
      ·
        refine ⟨187525737626497113630350189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125017158417664742420233459 187525737626497113630350189)
        ·
          refine ⟨70322151609936417611381321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187525737626497113630350189 70322151609936417611381321)
          ·
            refine ⟨52741613707452313208535991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70322151609936417611381321 52741613707452313208535991)
            ·
              refine ⟨79112420561178469812803987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52741613707452313208535991 79112420561178469812803987)
              ·
                refine ⟨118668630841767704719205981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79112420561178469812803987 118668630841767704719205981)
                ·
                  refine ⟨44500736565662889269702243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118668630841767704719205981 44500736565662889269702243)
                  ·
                    refine ⟨66751104848494333904553365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44500736565662889269702243 66751104848494333904553365)
                    ·
                      refine ⟨3128958039773171901775939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66751104848494333904553365 3128958039773171901775939)
                      ·
                        rfl

theorem cell23_6093624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_6093624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093624 prefixEnd_6093624 := by exact prefixLift 6093624
  have htrace : WordTrace (prefixWord ++ tailWord_6093624) baseStart_6093624 baseEnd_6093624 := by
    simpa [prefixWord, tailWord_6093624, baseEnd_6093624] using wordTrace_append hprefix tailTrace_6093624
  have hstable : (prefixWord ++ tailWord_6093624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093624).length < 2 ^ (prefixWord ++ tailWord_6093624).sum := by decide
  have hdescent : baseEnd_6093624 < baseStart_6093624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093631 : List Nat := [1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 5]
def baseStart_6093631 : Nat := 118140960795 + 6093631 * 2 ^ 59
def prefixEnd_6093631 : Nat := 4983230072969 + 3 ^ 40 * 6093631 * 2
def baseEnd_6093631 : Nat := 3128961634137753374388407

theorem tailTrace_6093631 : CollatzResearch.WordTrace tailWord_6093631 prefixEnd_6093631 3128961634137753374388407 := by
  unfold tailWord_6093631
  simp only [CollatzResearch.WordTrace]
  refine ⟨222252981386823071164808747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148168654257882047443205831 222252981386823071164808747)
  ·
    refine ⟨333379472080234606747213121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222252981386823071164808747 333379472080234606747213121)
    ·
      refine ⟨250034604060175955060409841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333379472080234606747213121 250034604060175955060409841)
      ·
        refine ⟨187525953045131966295307381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250034604060175955060409841 187525953045131966295307381)
        ·
          refine ⟨17580558097981121840185067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 187525953045131966295307381 17580558097981121840185067)
          ·
            refine ⟨26370837146971682760277601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17580558097981121840185067 26370837146971682760277601)
            ·
              refine ⟨19778127860228762070208201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26370837146971682760277601 19778127860228762070208201)
              ·
                refine ⟨14833595895171571552656151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19778127860228762070208201 14833595895171571552656151)
                ·
                  refine ⟨22250393842757357328984227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14833595895171571552656151 22250393842757357328984227)
                  ·
                    refine ⟨33375590764136035993476341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22250393842757357328984227 33375590764136035993476341)
                    ·
                      refine ⟨3128961634137753374388407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33375590764136035993476341 3128961634137753374388407)
                      ·
                        rfl

theorem cell23_6093631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 5].length) (baseStart_6093631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093631 prefixEnd_6093631 := by exact prefixLift 6093631
  have htrace : WordTrace (prefixWord ++ tailWord_6093631) baseStart_6093631 baseEnd_6093631 := by
    simpa [prefixWord, tailWord_6093631, baseEnd_6093631] using wordTrace_append hprefix tailTrace_6093631
  have hstable : (prefixWord ++ tailWord_6093631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093631).length < 2 ^ (prefixWord ++ tailWord_6093631).sum := by decide
  have hdescent : baseEnd_6093631 < baseStart_6093631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093645 : List Nat := [1, 6, 1, 2, 2, 1, 1, 1, 3, 1, 4]
def baseStart_6093645 : Nat := 118140960795 + 6093645 * 2 ^ 59
def prefixEnd_6093645 : Nat := 4983230072969 + 3 ^ 40 * 6093645 * 2
def baseEnd_6093645 : Nat := 3128968822866916319613343

theorem tailTrace_6093645 : CollatzResearch.WordTrace tailWord_6093645 prefixEnd_6093645 3128968822866916319613343 := by
  unfold tailWord_6093645
  simp only [CollatzResearch.WordTrace]
  refine ⟨222253492008772351555818389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148168994672514901037212259 222253492008772351555818389)
  ·
    refine ⟨10418132437911203979178987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 222253492008772351555818389 10418132437911203979178987)
    ·
      refine ⟨15627198656866805968768481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10418132437911203979178987 15627198656866805968768481)
      ·
        refine ⟨11720398992650104476576361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15627198656866805968768481 11720398992650104476576361)
        ·
          refine ⟨8790299244487578357432271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11720398992650104476576361 8790299244487578357432271)
          ·
            refine ⟨13185448866731367536148407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8790299244487578357432271 13185448866731367536148407)
            ·
              refine ⟨19778173300097051304222611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13185448866731367536148407 19778173300097051304222611)
              ·
                refine ⟨29667259950145576956333917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19778173300097051304222611 29667259950145576956333917)
                ·
                  refine ⟨11125222481304591358625219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29667259950145576956333917 11125222481304591358625219)
                  ·
                    refine ⟨16687833721956887037937829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11125222481304591358625219 16687833721956887037937829)
                    ·
                      refine ⟨3128968822866916319613343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16687833721956887037937829 3128968822866916319613343)
                      ·
                        rfl

theorem cell23_6093645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_6093645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093645 prefixEnd_6093645 := by exact prefixLift 6093645
  have htrace : WordTrace (prefixWord ++ tailWord_6093645) baseStart_6093645 baseEnd_6093645 := by
    simpa [prefixWord, tailWord_6093645, baseEnd_6093645] using wordTrace_append hprefix tailTrace_6093645
  have hstable : (prefixWord ++ tailWord_6093645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093645).length < 2 ^ (prefixWord ++ tailWord_6093645).sum := by decide
  have hdescent : baseEnd_6093645 < baseStart_6093645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093648 : List Nat := [2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 3]
def baseStart_6093648 : Nat := 118140960795 + 6093648 * 2 ^ 59
def prefixEnd_6093648 : Nat := 4983230072969 + 3 ^ 40 * 6093648 * 2
def baseEnd_6093648 : Nat := 3128970363308879807875829

theorem tailTrace_6093648 : CollatzResearch.WordTrace tailWord_6093648 prefixEnd_6093648 3128970363308879807875829 := by
  unfold tailWord_6093648
  simp only [CollatzResearch.WordTrace]
  refine ⟨111126800713880741534088799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148169067618507655378785065 111126800713880741534088799)
  ·
    refine ⟨166690201070821112301133199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111126800713880741534088799 166690201070821112301133199)
    ·
      refine ⟨250035301606231668451699799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166690201070821112301133199 250035301606231668451699799)
      ·
        refine ⟨375052952409347502677549699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250035301606231668451699799 375052952409347502677549699)
        ·
          refine ⟨562579428614021254016324549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375052952409347502677549699 562579428614021254016324549)
          ·
            refine ⟨105483642865128985128060853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 562579428614021254016324549 105483642865128985128060853)
            ·
              refine ⟨9889091518605842355755705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 105483642865128985128060853 9889091518605842355755705)
              ·
                refine ⟨7416818638954381766816779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9889091518605842355755705 7416818638954381766816779)
                ·
                  refine ⟨11125227958431572650225169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7416818638954381766816779 11125227958431572650225169)
                  ·
                    refine ⟨8343920968823679487668877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11125227958431572650225169 8343920968823679487668877)
                    ·
                      refine ⟨3128970363308879807875829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8343920968823679487668877 3128970363308879807875829)
                      ·
                        rfl

theorem cell23_6093648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 3].length) (baseStart_6093648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093648 prefixEnd_6093648 := by exact prefixLift 6093648
  have htrace : WordTrace (prefixWord ++ tailWord_6093648) baseStart_6093648 baseEnd_6093648 := by
    simpa [prefixWord, tailWord_6093648, baseEnd_6093648] using wordTrace_append hprefix tailTrace_6093648
  have hstable : (prefixWord ++ tailWord_6093648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093648).length < 2 ^ (prefixWord ++ tailWord_6093648).sum := by decide
  have hdescent : baseEnd_6093648 < baseStart_6093648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093722 : List Nat := [3, 1, 1, 4, 3, 1, 1, 3, 1, 3, 2]
def baseStart_6093722 : Nat := 118140960795 + 6093722 * 2 ^ 59
def prefixEnd_6093722 : Nat := 4983230072969 + 3 ^ 40 * 6093722 * 2
def baseEnd_6093722 : Nat := 3129008360877312518350489

theorem tailTrace_6093722 : CollatzResearch.WordTrace tailWord_6093722 prefixEnd_6093722 3129008360877312518350489 := by
  unfold tailWord_6093722
  simp only [CollatzResearch.WordTrace]
  refine ⟨55564075107373348426592855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148170866952995595804247613 55564075107373348426592855)
  ·
    refine ⟨83346112661060022639889283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55564075107373348426592855 83346112661060022639889283)
    ·
      refine ⟨125019168991590033959833925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83346112661060022639889283 125019168991590033959833925)
      ·
        refine ⟨23441094185923131367468861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125019168991590033959833925 23441094185923131367468861)
        ·
          refine ⟨8790410319721174262800823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23441094185923131367468861 8790410319721174262800823)
          ·
            refine ⟨13185615479581761394201235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8790410319721174262800823 13185615479581761394201235)
            ·
              refine ⟨19778423219372642091301853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13185615479581761394201235 19778423219372642091301853)
              ·
                refine ⟨7416908707264740784238195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19778423219372642091301853 7416908707264740784238195)
                ·
                  refine ⟨11125363060897111176357293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7416908707264740784238195 11125363060897111176357293)
                  ·
                    refine ⟨4172011147836416691133985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11125363060897111176357293 4172011147836416691133985)
                    ·
                      refine ⟨3129008360877312518350489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4172011147836416691133985 3129008360877312518350489)
                      ·
                        rfl

theorem cell23_6093722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_6093722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093722 prefixEnd_6093722 := by exact prefixLift 6093722
  have htrace : WordTrace (prefixWord ++ tailWord_6093722) baseStart_6093722 baseEnd_6093722 := by
    simpa [prefixWord, tailWord_6093722, baseEnd_6093722] using wordTrace_append hprefix tailTrace_6093722
  have hstable : (prefixWord ++ tailWord_6093722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093722).length < 2 ^ (prefixWord ++ tailWord_6093722).sum := by decide
  have hdescent : baseEnd_6093722 < baseStart_6093722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093731 : List Nat := [1, 1, 1, 4, 1, 2, 3, 2, 2, 2, 4]
def baseStart_6093731 : Nat := 118140960795 + 6093731 * 2 ^ 59
def prefixEnd_6093731 : Nat := 4983230072969 + 3 ^ 40 * 6093731 * 2
def baseEnd_6093731 : Nat := 3129012982203202983137947

theorem tailTrace_6093731 : CollatzResearch.WordTrace tailWord_6093731 prefixEnd_6093731 3129012982203202983137947 := by
  unfold tailWord_6093731
  simp only [CollatzResearch.WordTrace]
  refine ⟨222256628686460788243449047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148171085790973858828966031 222256628686460788243449047)
  ·
    refine ⟨333384943029691182365173571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222256628686460788243449047 333384943029691182365173571)
    ·
      refine ⟨500077414544536773547760357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333384943029691182365173571 500077414544536773547760357)
      ·
        refine ⟨93764515227100645040205067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 500077414544536773547760357 93764515227100645040205067)
        ·
          refine ⟨140646772840650967560307601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93764515227100645040205067 140646772840650967560307601)
          ·
            refine ⟨105485079630488225670230701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140646772840650967560307601 105485079630488225670230701)
            ·
              refine ⟨39556904861433084626336513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105485079630488225670230701 39556904861433084626336513)
              ·
                refine ⟨29667678646074813469752385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39556904861433084626336513 29667678646074813469752385)
                ·
                  refine ⟨22250758984556110102314289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29667678646074813469752385 22250758984556110102314289)
                  ·
                    refine ⟨16688069238417082576735717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22250758984556110102314289 16688069238417082576735717)
                    ·
                      refine ⟨3129012982203202983137947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16688069238417082576735717 3129012982203202983137947)
                      ·
                        rfl

theorem cell23_6093731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_6093731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093731 prefixEnd_6093731 := by exact prefixLift 6093731
  have htrace : WordTrace (prefixWord ++ tailWord_6093731) baseStart_6093731 baseEnd_6093731 := by
    simpa [prefixWord, tailWord_6093731, baseEnd_6093731] using wordTrace_append hprefix tailTrace_6093731
  have hstable : (prefixWord ++ tailWord_6093731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093731).length < 2 ^ (prefixWord ++ tailWord_6093731).sum := by decide
  have hdescent : baseEnd_6093731 < baseStart_6093731 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093771 : List Nat := [1, 1, 1, 1, 3, 5, 2, 1, 1, 7]
def baseStart_6093771 : Nat := 118140960795 + 6093771 * 2 ^ 59
def prefixEnd_6093771 : Nat := 4983230072969 + 3 ^ 40 * 6093771 * 2
def baseEnd_6093771 : Nat := 1043011173809794275545921

theorem tailTrace_6093771 : CollatzResearch.WordTrace tailWord_6093771 prefixEnd_6093771 1043011173809794275545921 := by
  unfold tailWord_6093771
  simp only [CollatzResearch.WordTrace]
  refine ⟨222258087606315875074905167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148172058404210583383270111 222258087606315875074905167)
  ·
    refine ⟨333387131409473812612357751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222258087606315875074905167 333387131409473812612357751)
    ·
      refine ⟨500080697114210718918536627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333387131409473812612357751 500080697114210718918536627)
      ·
        refine ⟨750121045671316078377804941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500080697114210718918536627 750121045671316078377804941)
        ·
          refine ⟨281295392126743529391676853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 750121045671316078377804941 281295392126743529391676853)
          ·
            refine ⟨26371443011882205880469705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 281295392126743529391676853 26371443011882205880469705)
            ·
              refine ⟨19778582258911654410352279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26371443011882205880469705 19778582258911654410352279)
              ·
                refine ⟨29667873388367481615528419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19778582258911654410352279 29667873388367481615528419)
                ·
                  refine ⟨44501810082551222423292629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29667873388367481615528419 44501810082551222423292629)
                  ·
                    refine ⟨1043011173809794275545921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44501810082551222423292629 1043011173809794275545921)
                    ·
                      rfl

theorem cell23_6093771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 7].length) (baseStart_6093771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093771 prefixEnd_6093771 := by exact prefixLift 6093771
  have htrace : WordTrace (prefixWord ++ tailWord_6093771) baseStart_6093771 baseEnd_6093771 := by
    simpa [prefixWord, tailWord_6093771, baseEnd_6093771] using wordTrace_append hprefix tailTrace_6093771
  have hstable : (prefixWord ++ tailWord_6093771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093771).length < 2 ^ (prefixWord ++ tailWord_6093771).sum := by decide
  have hdescent : baseEnd_6093771 < baseStart_6093771 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093775 : List Nat := [1, 1, 2, 1, 1, 8, 1, 3, 5]
def baseStart_6093775 : Nat := 118140960795 + 6093775 * 2 ^ 59
def prefixEnd_6093775 : Nat := 4983230072969 + 3 ^ 40 * 6093775 * 2
def baseEnd_6093775 : Nat := 347670619483555645665305

theorem tailTrace_6093775 : CollatzResearch.WordTrace tailWord_6093775 prefixEnd_6093775 347670619483555645665305 := by
  unfold tailWord_6093775
  simp only [CollatzResearch.WordTrace]
  refine ⟨222258233498301383758050779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148172155665534255838700519 222258233498301383758050779)
  ·
    refine ⟨333387350247452075637076169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222258233498301383758050779 333387350247452075637076169)
    ·
      refine ⟨250040512685589056727807127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333387350247452075637076169 250040512685589056727807127)
      ·
        refine ⟨375060769028383585091710691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250040512685589056727807127 375060769028383585091710691)
        ·
          refine ⟨562591153542575377637566037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375060769028383585091710691 562591153542575377637566037)
          ·
            refine ⟨6592865080577055206690227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 562591153542575377637566037 6592865080577055206690227)
            ·
              refine ⟨9889297620865582810035341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6592865080577055206690227 9889297620865582810035341)
              ·
                refine ⟨3708486607824593553763253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9889297620865582810035341 3708486607824593553763253)
                ·
                  refine ⟨347670619483555645665305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3708486607824593553763253 347670619483555645665305)
                  ·
                    rfl

theorem cell23_6093775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 3, 5].length) (baseStart_6093775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093775 prefixEnd_6093775 := by exact prefixLift 6093775
  have htrace : WordTrace (prefixWord ++ tailWord_6093775) baseStart_6093775 baseEnd_6093775 := by
    simpa [prefixWord, tailWord_6093775, baseEnd_6093775] using wordTrace_append hprefix tailTrace_6093775
  have hstable : (prefixWord ++ tailWord_6093775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093775).length < 2 ^ (prefixWord ++ tailWord_6093775).sum := by decide
  have hdescent : baseEnd_6093775 < baseStart_6093775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093808 : List Nat := [2, 1, 1, 1, 3, 2, 1, 3, 1, 6, 2]
def baseStart_6093808 : Nat := 118140960795 + 6093808 * 2 ^ 59
def prefixEnd_6093808 : Nat := 4983230072969 + 3 ^ 40 * 6093808 * 2
def baseEnd_6093808 : Nat := 3129052520213599181875093

theorem tailTrace_6093808 : CollatzResearch.WordTrace tailWord_6093808 prefixEnd_6093808 3129052520213599181875093 := by
  unfold tailWord_6093808
  simp only [CollatzResearch.WordTrace]
  refine ⟨111129718553590915197001039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148172958071454553596001385 111129718553590915197001039)
  ·
    refine ⟨166694577830386372795501559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111129718553590915197001039 166694577830386372795501559)
    ·
      refine ⟨250041866745579559193252339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166694577830386372795501559 250041866745579559193252339)
      ·
        refine ⟨375062800118369338789878509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250041866745579559193252339 375062800118369338789878509)
        ·
          refine ⟨140648550044388502046204441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 375062800118369338789878509 140648550044388502046204441)
          ·
            refine ⟨105486412533291376534653331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140648550044388502046204441 105486412533291376534653331)
            ·
              refine ⟨158229618799937064801979997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105486412533291376534653331 158229618799937064801979997)
              ·
                refine ⟨59336107049976399300742499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158229618799937064801979997 59336107049976399300742499)
                ·
                  refine ⟨89004160574964598951113749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59336107049976399300742499 89004160574964598951113749)
                  ·
                    refine ⟨4172070026951465575833457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 89004160574964598951113749 4172070026951465575833457)
                    ·
                      refine ⟨3129052520213599181875093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4172070026951465575833457 3129052520213599181875093)
                      ·
                        rfl

theorem cell23_6093808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 1, 6, 2].length) (baseStart_6093808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093808 prefixEnd_6093808 := by exact prefixLift 6093808
  have htrace : WordTrace (prefixWord ++ tailWord_6093808) baseStart_6093808 baseEnd_6093808 := by
    simpa [prefixWord, tailWord_6093808, baseEnd_6093808] using wordTrace_append hprefix tailTrace_6093808
  have hstable : (prefixWord ++ tailWord_6093808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093808).length < 2 ^ (prefixWord ++ tailWord_6093808).sum := by decide
  have hdescent : baseEnd_6093808 < baseStart_6093808 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093818 : List Nat := [3, 1, 1, 1, 1, 2, 1, 6, 3, 4]
def baseStart_6093818 : Nat := 118140960795 + 6093818 * 2 ^ 59
def prefixEnd_6093818 : Nat := 4983230072969 + 3 ^ 40 * 6093818 * 2
def baseEnd_6093818 : Nat := 1043019218340048047583349

theorem tailTrace_6093818 : CollatzResearch.WordTrace tailWord_6093818 prefixEnd_6093818 1043019218340048047583349 := by
  unfold tailWord_6093818
  simp only [CollatzResearch.WordTrace]
  refine ⟨55564950459286400525466527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148173201224763734734577405 55564950459286400525466527)
  ·
    refine ⟨83347425688929600788199791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55564950459286400525466527 83347425688929600788199791)
    ·
      refine ⟨125021138533394401182299687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83347425688929600788199791 125021138533394401182299687)
      ·
        refine ⟨187531707800091601773449531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125021138533394401182299687 187531707800091601773449531)
        ·
          refine ⟨281297561700137402660174297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187531707800091601773449531 281297561700137402660174297)
          ·
            refine ⟨210973171275103051995130723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281297561700137402660174297 210973171275103051995130723)
            ·
              refine ⟨316459756912654577992696085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210973171275103051995130723 316459756912654577992696085)
              ·
                refine ⟨14834051105280683343407629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 316459756912654577992696085 14834051105280683343407629)
                ·
                  refine ⟨5562769164480256253777861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14834051105280683343407629 5562769164480256253777861)
                  ·
                    refine ⟨1043019218340048047583349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5562769164480256253777861 1043019218340048047583349)
                    ·
                      rfl

theorem cell23_6093818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 3, 4].length) (baseStart_6093818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093818 prefixEnd_6093818 := by exact prefixLift 6093818
  have htrace : WordTrace (prefixWord ++ tailWord_6093818) baseStart_6093818 baseEnd_6093818 := by
    simpa [prefixWord, tailWord_6093818, baseEnd_6093818] using wordTrace_append hprefix tailTrace_6093818
  have hstable : (prefixWord ++ tailWord_6093818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093818).length < 2 ^ (prefixWord ++ tailWord_6093818).sum := by decide
  have hdescent : baseEnd_6093818 < baseStart_6093818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093821 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 1, 3, 6]
def baseStart_6093821 : Nat := 118140960795 + 6093821 * 2 ^ 59
def prefixEnd_6093821 : Nat := 4983230072969 + 3 ^ 40 * 6093821 * 2
def baseEnd_6093821 : Nat := 3129059195462107631012533

theorem tailTrace_6093821 : CollatzResearch.WordTrace tailWord_6093821 prefixEnd_6093821 3129059195462107631012533 := by
  unfold tailWord_6093821
  simp only [CollatzResearch.WordTrace]
  refine ⟨222259911256134733614225317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148173274170756489076150211 222259911256134733614225317)
  ·
    refine ⟨41673733360525262552667247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222259911256134733614225317 41673733360525262552667247)
    ·
      refine ⟨62510600040787893829000871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41673733360525262552667247 62510600040787893829000871)
      ·
        refine ⟨93765900061181840743501307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62510600040787893829000871 93765900061181840743501307)
        ·
          refine ⟨140648850091772761115251961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93765900061181840743501307 140648850091772761115251961)
          ·
            refine ⟨105486637568829570836438971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140648850091772761115251961 105486637568829570836438971)
            ·
              refine ⟨158229956353244356254658457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105486637568829570836438971 158229956353244356254658457)
              ·
                refine ⟨118672467264933267190993843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158229956353244356254658457 118672467264933267190993843)
                ·
                  refine ⟨178008700897399900786490765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118672467264933267190993843 178008700897399900786490765)
                  ·
                    refine ⟨66753262836524962794934037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 178008700897399900786490765 66753262836524962794934037)
                    ·
                      refine ⟨3129059195462107631012533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66753262836524962794934037 3129059195462107631012533)
                      ·
                        rfl

theorem cell23_6093821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_6093821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093821 prefixEnd_6093821 := by exact prefixLift 6093821
  have htrace : WordTrace (prefixWord ++ tailWord_6093821) baseStart_6093821 baseEnd_6093821 := by
    simpa [prefixWord, tailWord_6093821, baseEnd_6093821] using wordTrace_append hprefix tailTrace_6093821
  have hstable : (prefixWord ++ tailWord_6093821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093821).length < 2 ^ (prefixWord ++ tailWord_6093821).sum := by decide
  have hdescent : baseEnd_6093821 < baseStart_6093821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093822 : List Nat := [4, 2, 2, 2, 2, 1, 2, 1, 2, 5]
def baseStart_6093822 : Nat := 118140960795 + 6093822 * 2 ^ 59
def prefixEnd_6093822 : Nat := 4983230072969 + 3 ^ 40 * 6093822 * 2
def baseEnd_6093822 : Nat := 1043019902980920709033343

theorem tailTrace_6093822 : CollatzResearch.WordTrace tailWord_6093822 prefixEnd_6093822 1043019902980920709033343 := by
  unfold tailWord_6093822
  simp only [CollatzResearch.WordTrace]
  refine ⟨27782493466141388848126465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148173298486087407190007813 27782493466141388848126465)
  ·
    refine ⟨20836870099606041636094849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27782493466141388848126465 20836870099606041636094849)
    ·
      refine ⟨15627652574704531227071137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20836870099606041636094849 15627652574704531227071137)
      ·
        refine ⟨11720739431028398420303353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15627652574704531227071137 11720739431028398420303353)
        ·
          refine ⟨8790554573271298815227515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11720739431028398420303353 8790554573271298815227515)
          ·
            refine ⟨13185831859906948222841273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8790554573271298815227515 13185831859906948222841273)
            ·
              refine ⟨9889373894930211167130955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13185831859906948222841273 9889373894930211167130955)
              ·
                refine ⟨14834060842395316750696433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9889373894930211167130955 14834060842395316750696433)
                ·
                  refine ⟨11125545631796487563022325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14834060842395316750696433 11125545631796487563022325)
                  ·
                    refine ⟨1043019902980920709033343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11125545631796487563022325 1043019902980920709033343)
                    ·
                      rfl

theorem cell23_6093822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_6093822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093822 prefixEnd_6093822 := by exact prefixLift 6093822
  have htrace : WordTrace (prefixWord ++ tailWord_6093822) baseStart_6093822 baseEnd_6093822 := by
    simpa [prefixWord, tailWord_6093822, baseEnd_6093822] using wordTrace_append hprefix tailTrace_6093822
  have hstable : (prefixWord ++ tailWord_6093822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093822).length < 2 ^ (prefixWord ++ tailWord_6093822).sum := by decide
  have hdescent : baseEnd_6093822 < baseStart_6093822 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093825 : List Nat := [1, 2, 4, 1, 2, 3, 2, 1, 2, 1, 4]
def baseStart_6093825 : Nat := 118140960795 + 6093825 * 2 ^ 59
def prefixEnd_6093825 : Nat := 4983230072969 + 3 ^ 40 * 6093825 * 2
def baseEnd_6093825 : Nat := 3129061249384725615362515

theorem tailTrace_6093825 : CollatzResearch.WordTrace tailWord_6093825 prefixEnd_6093825 3129061249384725615362515 := by
  unfold tailWord_6093825
  simp only [CollatzResearch.WordTrace]
  refine ⟨222260057148120242297370929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148173371432080161531580619 222260057148120242297370929)
  ·
    refine ⟨166695042861090181723028197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222260057148120242297370929 166695042861090181723028197)
    ·
      refine ⟨31255320536454409073067787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166695042861090181723028197 31255320536454409073067787)
      ·
        refine ⟨46882980804681613609601681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31255320536454409073067787 46882980804681613609601681)
        ·
          refine ⟨35162235603511210207201261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46882980804681613609601681 35162235603511210207201261)
          ·
            refine ⟨13185838351316703827700473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35162235603511210207201261 13185838351316703827700473)
            ·
              refine ⟨9889378763487527870775355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13185838351316703827700473 9889378763487527870775355)
              ·
                refine ⟨14834068145231291806163033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9889378763487527870775355 14834068145231291806163033)
                ·
                  refine ⟨11125551108923468854622275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14834068145231291806163033 11125551108923468854622275)
                  ·
                    refine ⟨16688326663385203281933413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11125551108923468854622275 16688326663385203281933413)
                    ·
                      refine ⟨3129061249384725615362515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16688326663385203281933413 3129061249384725615362515)
                      ·
                        rfl

theorem cell23_6093825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_6093825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093825 prefixEnd_6093825 := by exact prefixLift 6093825
  have htrace : WordTrace (prefixWord ++ tailWord_6093825) baseStart_6093825 baseEnd_6093825 := by
    simpa [prefixWord, tailWord_6093825, baseEnd_6093825] using wordTrace_append hprefix tailTrace_6093825
  have hstable : (prefixWord ++ tailWord_6093825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093825).length < 2 ^ (prefixWord ++ tailWord_6093825).sum := by decide
  have hdescent : baseEnd_6093825 < baseStart_6093825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093845 : List Nat := [1, 3, 2, 1, 4, 1, 2, 2, 2, 2, 3]
def baseStart_6093845 : Nat := 118140960795 + 6093845 * 2 ^ 59
def prefixEnd_6093845 : Nat := 4983230072969 + 3 ^ 40 * 6093845 * 2
def baseEnd_6093845 : Nat := 3129071518997815537112423

theorem tailTrace_6093845 : CollatzResearch.WordTrace tailWord_6093845 prefixEnd_6093845 3129071518997815537112423 := by
  unfold tailWord_6093845
  simp only [CollatzResearch.WordTrace]
  refine ⟨222260786608047785713098989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148173857738698523808732659 222260786608047785713098989)
  ·
    refine ⟨83347794978017919642412121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222260786608047785713098989 83347794978017919642412121)
    ·
      refine ⟨62510846233513439731809091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83347794978017919642412121 62510846233513439731809091)
      ·
        refine ⟨93766269350270159597713637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62510846233513439731809091 93766269350270159597713637)
        ·
          refine ⟨17581175503175654924571307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93766269350270159597713637 17581175503175654924571307)
          ·
            refine ⟨26371763254763482386856961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17581175503175654924571307 26371763254763482386856961)
            ·
              refine ⟨19778822441072611790142721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26371763254763482386856961 19778822441072611790142721)
              ·
                refine ⟨14834116830804458842607041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19778822441072611790142721 14834116830804458842607041)
                ·
                  refine ⟨11125587623103344131955281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14834116830804458842607041 11125587623103344131955281)
                  ·
                    refine ⟨8344190717327508098966461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11125587623103344131955281 8344190717327508098966461)
                    ·
                      refine ⟨3129071518997815537112423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8344190717327508098966461 3129071518997815537112423)
                      ·
                        rfl

theorem cell23_6093845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 2, 2, 3].length) (baseStart_6093845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093845 prefixEnd_6093845 := by exact prefixLift 6093845
  have htrace : WordTrace (prefixWord ++ tailWord_6093845) baseStart_6093845 baseEnd_6093845 := by
    simpa [prefixWord, tailWord_6093845, baseEnd_6093845] using wordTrace_append hprefix tailTrace_6093845
  have hstable : (prefixWord ++ tailWord_6093845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093845).length < 2 ^ (prefixWord ++ tailWord_6093845).sum := by decide
  have hdescent : baseEnd_6093845 < baseStart_6093845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093848 : List Nat := [2, 1, 2, 3, 2, 2, 1, 4, 6]
def baseStart_6093848 : Nat := 118140960795 + 6093848 * 2 ^ 59
def prefixEnd_6093848 : Nat := 4983230072969 + 3 ^ 40 * 6093848 * 2
def baseEnd_6093848 : Nat := 347674784382197669486101

theorem tailTrace_6093848 : CollatzResearch.WordTrace tailWord_6093848 prefixEnd_6093848 347674784382197669486101 := by
  unfold tailWord_6093848
  simp only [CollatzResearch.WordTrace]
  refine ⟨111130448013518458612729099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148173930684691278150305465 111130448013518458612729099)
  ·
    refine ⟨166695672020277687919093649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111130448013518458612729099 166695672020277687919093649)
    ·
      refine ⟨125021754015208265939320237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166695672020277687919093649 125021754015208265939320237)
      ·
        refine ⟨46883157755703099727245089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125021754015208265939320237 46883157755703099727245089)
        ·
          refine ⟨35162368316777324795433817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46883157755703099727245089 35162368316777324795433817)
          ·
            refine ⟨26371776237582993596575363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35162368316777324795433817 26371776237582993596575363)
            ·
              refine ⟨39557664356374490394863045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26371776237582993596575363 39557664356374490394863045)
              ·
                refine ⟨7417062066820216949036821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39557664356374490394863045 7417062066820216949036821)
                ·
                  refine ⟨347674784382197669486101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7417062066820216949036821 347674784382197669486101)
                  ·
                    rfl

theorem cell23_6093848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 4, 6].length) (baseStart_6093848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093848 prefixEnd_6093848 := by exact prefixLift 6093848
  have htrace : WordTrace (prefixWord ++ tailWord_6093848) baseStart_6093848 baseEnd_6093848 := by
    simpa [prefixWord, tailWord_6093848, baseEnd_6093848] using wordTrace_append hprefix tailTrace_6093848
  have hstable : (prefixWord ++ tailWord_6093848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093848).length < 2 ^ (prefixWord ++ tailWord_6093848).sum := by decide
  have hdescent : baseEnd_6093848 < baseStart_6093848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093871 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 5]
def baseStart_6093871 : Nat := 118140960795 + 6093871 * 2 ^ 59
def prefixEnd_6093871 : Nat := 4983230072969 + 3 ^ 40 * 6093871 * 2
def baseEnd_6093871 : Nat := 3129084869494832435387303

theorem tailTrace_6093871 : CollatzResearch.WordTrace tailWord_6093871 prefixEnd_6093871 3129084869494832435387303 := by
  unfold tailWord_6093871
  simp only [CollatzResearch.WordTrace]
  refine ⟨222261734905953592153545467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148174489937302394769030311 222261734905953592153545467)
  ·
    refine ⟨333392602358930388230318201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222261734905953592153545467 333392602358930388230318201)
    ·
      refine ⟨250044451769197791172738651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333392602358930388230318201 250044451769197791172738651)
      ·
        refine ⟨375066677653796686759107977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250044451769197791172738651 375066677653796686759107977)
        ·
          refine ⟨281300008240347515069330983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 375066677653796686759107977 281300008240347515069330983)
          ·
            refine ⟨421950012360521272603996475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281300008240347515069330983 421950012360521272603996475)
            ·
              refine ⟨632925018540781908905994713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 421950012360521272603996475 632925018540781908905994713)
              ·
                refine ⟨474693763905586431679496035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 632925018540781908905994713 474693763905586431679496035)
                ·
                  refine ⟨712040645858379647519244053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 474693763905586431679496035 712040645858379647519244053)
                  ·
                    refine ⟨33376905274611545977464565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 712040645858379647519244053 33376905274611545977464565)
                    ·
                      refine ⟨3129084869494832435387303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33376905274611545977464565 3129084869494832435387303)
                      ·
                        rfl

theorem cell23_6093871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 5].length) (baseStart_6093871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093871 prefixEnd_6093871 := by exact prefixLift 6093871
  have htrace : WordTrace (prefixWord ++ tailWord_6093871) baseStart_6093871 baseEnd_6093871 := by
    simpa [prefixWord, tailWord_6093871, baseEnd_6093871] using wordTrace_append hprefix tailTrace_6093871
  have hstable : (prefixWord ++ tailWord_6093871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093871).length < 2 ^ (prefixWord ++ tailWord_6093871).sum := by decide
  have hdescent : baseEnd_6093871 < baseStart_6093871 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093895 : List Nat := [1, 1, 4, 1, 3, 3, 1, 3, 1, 5]
def baseStart_6093895 : Nat := 118140960795 + 6093895 * 2 ^ 59
def prefixEnd_6093895 : Nat := 4983230072969 + 3 ^ 40 * 6093895 * 2
def baseEnd_6093895 : Nat := 1043032397676846780495731

theorem tailTrace_6093895 : CollatzResearch.WordTrace tailWord_6093895 prefixEnd_6093895 1043032397676846780495731 := by
  unfold tailWord_6093895
  simp only [CollatzResearch.WordTrace]
  refine ⟨222262610257866644252419139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148175073505244429501612759 222262610257866644252419139)
  ·
    refine ⟨333393915386799966378628709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222262610257866644252419139 333393915386799966378628709)
    ·
      refine ⟨62511359135024993695992883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 333393915386799966378628709 62511359135024993695992883)
      ·
        refine ⟨93767038702537490543989325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62511359135024993695992883 93767038702537490543989325)
        ·
          refine ⟨35162639513451558953995997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93767038702537490543989325 35162639513451558953995997)
          ·
            refine ⟨13185989817544334607748499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35162639513451558953995997 13185989817544334607748499)
            ·
              refine ⟨19778984726316501911622749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13185989817544334607748499 19778984726316501911622749)
              ·
                refine ⟨7417119272368688216858531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19778984726316501911622749 7417119272368688216858531)
                ·
                  refine ⟨11125678908553032325287797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7417119272368688216858531 11125678908553032325287797)
                  ·
                    refine ⟨1043032397676846780495731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11125678908553032325287797 1043032397676846780495731)
                    ·
                      rfl

theorem cell23_6093895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 3, 1, 5].length) (baseStart_6093895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093895 prefixEnd_6093895 := by exact prefixLift 6093895
  have htrace : WordTrace (prefixWord ++ tailWord_6093895) baseStart_6093895 baseEnd_6093895 := by
    simpa [prefixWord, tailWord_6093895, baseEnd_6093895] using wordTrace_append hprefix tailTrace_6093895
  have hstable : (prefixWord ++ tailWord_6093895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093895).length < 2 ^ (prefixWord ++ tailWord_6093895).sum := by decide
  have hdescent : baseEnd_6093895 < baseStart_6093895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093908 : List Nat := [2, 4, 1, 1, 1, 1, 2, 2, 3, 6]
def baseStart_6093908 : Nat := 118140960795 + 6093908 * 2 ^ 59
def prefixEnd_6093908 : Nat := 4983230072969 + 3 ^ 40 * 6093908 * 2
def baseEnd_6093908 : Nat := 1043034622759682930208211

theorem tailTrace_6093908 : CollatzResearch.WordTrace tailWord_6093908 prefixEnd_6093908 1043034622759682930208211 := by
  unfold tailWord_6093908
  simp only [CollatzResearch.WordTrace]
  refine ⟨111131542203409773736321189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148175389604546364981761585 111131542203409773736321189)
  ·
    refine ⟨20837164163139332575560223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111131542203409773736321189 20837164163139332575560223)
    ·
      refine ⟨31255746244708998863340335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20837164163139332575560223 31255746244708998863340335)
      ·
        refine ⟨46883619367063498295010503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31255746244708998863340335 46883619367063498295010503)
        ·
          refine ⟨70325429050595247442515755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46883619367063498295010503 70325429050595247442515755)
          ·
            refine ⟨105488143575892871163773633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70325429050595247442515755 105488143575892871163773633)
            ·
              refine ⟨79116107681919653372830225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105488143575892871163773633 79116107681919653372830225)
              ·
                refine ⟨59337080761439740029622669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79116107681919653372830225 59337080761439740029622669)
                ·
                  refine ⟨22251405285539902511108501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59337080761439740029622669 22251405285539902511108501)
                  ·
                    refine ⟨1043034622759682930208211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22251405285539902511108501 1043034622759682930208211)
                    ·
                      rfl

theorem cell23_6093908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_6093908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093908 prefixEnd_6093908 := by exact prefixLift 6093908
  have htrace : WordTrace (prefixWord ++ tailWord_6093908) baseStart_6093908 baseEnd_6093908 := by
    simpa [prefixWord, tailWord_6093908, baseEnd_6093908] using wordTrace_append hprefix tailTrace_6093908
  have hstable : (prefixWord ++ tailWord_6093908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093908).length < 2 ^ (prefixWord ++ tailWord_6093908).sum := by decide
  have hdescent : baseEnd_6093908 < baseStart_6093908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093932 : List Nat := [2, 2, 1, 1, 3, 2, 1, 4, 3, 2, 2]
def baseStart_6093932 : Nat := 118140960795 + 6093932 * 2 ^ 59
def prefixEnd_6093932 : Nat := 4983230072969 + 3 ^ 40 * 6093932 * 2
def baseEnd_6093932 : Nat := 3129116191814756696724523

theorem tailTrace_6093932 : CollatzResearch.WordTrace tailWord_6093932 prefixEnd_6093932 3129116191814756696724523 := by
  unfold tailWord_6093932
  simp only [CollatzResearch.WordTrace]
  refine ⟨111131979879366299785758025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148175973172488399714344033 111131979879366299785758025)
  ·
    refine ⟨83348984909524724839318519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111131979879366299785758025 83348984909524724839318519)
    ·
      refine ⟨125023477364287087258977779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83348984909524724839318519 125023477364287087258977779)
      ·
        refine ⟨187535216046430630888466669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125023477364287087258977779 187535216046430630888466669)
        ·
          refine ⟨70325706017411486583175001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187535216046430630888466669 70325706017411486583175001)
          ·
            refine ⟨52744279513058614937381251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70325706017411486583175001 52744279513058614937381251)
            ·
              refine ⟨79116419269587922406071877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52744279513058614937381251 79116419269587922406071877)
              ·
                refine ⟨14834328613047735451138477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79116419269587922406071877 14834328613047735451138477)
                ·
                  refine ⟨5562873229892900794176929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14834328613047735451138477 5562873229892900794176929)
                  ·
                    refine ⟨4172154922419675595632697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5562873229892900794176929 4172154922419675595632697)
                    ·
                      refine ⟨3129116191814756696724523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4172154922419675595632697 3129116191814756696724523)
                      ·
                        rfl

theorem cell23_6093932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 2, 2].length) (baseStart_6093932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093932 prefixEnd_6093932 := by exact prefixLift 6093932
  have htrace : WordTrace (prefixWord ++ tailWord_6093932) baseStart_6093932 baseEnd_6093932 := by
    simpa [prefixWord, tailWord_6093932, baseEnd_6093932] using wordTrace_append hprefix tailTrace_6093932
  have hstable : (prefixWord ++ tailWord_6093932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093932).length < 2 ^ (prefixWord ++ tailWord_6093932).sum := by decide
  have hdescent : baseEnd_6093932 < baseStart_6093932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093938 : List Nat := [3, 2, 1, 2, 2, 1, 3, 9]
def baseStart_6093938 : Nat := 118140960795 + 6093938 * 2 ^ 59
def prefixEnd_6093938 : Nat := 4983230072969 + 3 ^ 40 * 6093938 * 2
def baseEnd_6093938 : Nat := 115893306396247543453685

theorem tailTrace_6093938 : CollatzResearch.WordTrace tailWord_6093938 prefixEnd_6093938 115893306396247543453685 := by
  unfold tailWord_6093938
  simp only [CollatzResearch.WordTrace]
  refine ⟨55566044649177715649058617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148176119064473908397489645 55566044649177715649058617)
  ·
    refine ⟨41674533486883286736793963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55566044649177715649058617 41674533486883286736793963)
    ·
      refine ⟨62511800230324930105190945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41674533486883286736793963 62511800230324930105190945)
      ·
        refine ⟨46883850172743697578893209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62511800230324930105190945 46883850172743697578893209)
        ·
          refine ⟨35162887629557773184169907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46883850172743697578893209 35162887629557773184169907)
          ·
            refine ⟨52744331444336659776254861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35162887629557773184169907 52744331444336659776254861)
            ·
              refine ⟨19779124291626247416095573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52744331444336659776254861 19779124291626247416095573)
              ·
                refine ⟨115893306396247543453685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19779124291626247416095573 115893306396247543453685)
                ·
                  rfl

theorem cell23_6093938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 9].length) (baseStart_6093938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093938 prefixEnd_6093938 := by exact prefixLift 6093938
  have htrace : WordTrace (prefixWord ++ tailWord_6093938) baseStart_6093938 baseEnd_6093938 := by
    simpa [prefixWord, tailWord_6093938, baseEnd_6093938] using wordTrace_append hprefix tailTrace_6093938
  have hstable : (prefixWord ++ tailWord_6093938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093938).length < 2 ^ (prefixWord ++ tailWord_6093938).sum := by decide
  have hdescent : baseEnd_6093938 < baseStart_6093938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093966 : List Nat := [4, 1, 1, 3, 2, 3, 1, 1, 3, 2, 2]
def baseStart_6093966 : Nat := 118140960795 + 6093966 * 2 ^ 59
def prefixEnd_6093966 : Nat := 4983230072969 + 3 ^ 40 * 6093966 * 2
def baseEnd_6093966 : Nat := 3129133650157009563699367

theorem tailTrace_6093966 : CollatzResearch.WordTrace tailWord_6093966 prefixEnd_6093966 3129133650157009563699367 := by
  unfold tailWord_6093966
  simp only [CollatzResearch.WordTrace]
  refine ⟨27783149980076177922281719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148176799893739615585502501 27783149980076177922281719)
  ·
    refine ⟨41674724970114266883422579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27783149980076177922281719 41674724970114266883422579)
    ·
      refine ⟨62512087455171400325133869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41674724970114266883422579 62512087455171400325133869)
      ·
        refine ⟨23442032795689275121925201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62512087455171400325133869 23442032795689275121925201)
        ·
          refine ⟨17581524596766956341443901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23442032795689275121925201 17581524596766956341443901)
          ·
            refine ⟨6593071723787608628041463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17581524596766956341443901 6593071723787608628041463)
            ·
              refine ⟨9889607585681412942062195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6593071723787608628041463 9889607585681412942062195)
              ·
                refine ⟨14834411378522119413093293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9889607585681412942062195 14834411378522119413093293)
                ·
                  refine ⟨5562904266945794779909985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14834411378522119413093293 5562904266945794779909985)
                  ·
                    refine ⟨4172178200209346084932489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5562904266945794779909985 4172178200209346084932489)
                    ·
                      refine ⟨3129133650157009563699367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4172178200209346084932489 3129133650157009563699367)
                      ·
                        rfl

theorem cell23_6093966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_6093966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093966 prefixEnd_6093966 := by exact prefixLift 6093966
  have htrace : WordTrace (prefixWord ++ tailWord_6093966) baseStart_6093966 baseEnd_6093966 := by
    simpa [prefixWord, tailWord_6093966, baseEnd_6093966] using wordTrace_append hprefix tailTrace_6093966
  have hstable : (prefixWord ++ tailWord_6093966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093966).length < 2 ^ (prefixWord ++ tailWord_6093966).sum := by decide
  have hdescent : baseEnd_6093966 < baseStart_6093966 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6093986 : List Nat := [3, 3, 1, 3, 2, 2, 1, 2, 1, 2, 3]
def baseStart_6093986 : Nat := 118140960795 + 6093986 * 2 ^ 59
def prefixEnd_6093986 : Nat := 4983230072969 + 3 ^ 40 * 6093986 * 2
def baseEnd_6093986 : Nat := 3129143919770099485449275

theorem tailTrace_6093986 : CollatzResearch.WordTrace tailWord_6093986 prefixEnd_6093986 3129143919770099485449275 := by
  unfold tailWord_6093986
  simp only [CollatzResearch.WordTrace]
  refine ⟨55566482325134241698495453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148177286200357977862654541 55566482325134241698495453)
  ·
    refine ⟨20837430871925340636935795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55566482325134241698495453 20837430871925340636935795)
    ·
      refine ⟨31256146307888010955403693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20837430871925340636935795 31256146307888010955403693)
      ·
        refine ⟨11721054865458004108276385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31256146307888010955403693 11721054865458004108276385)
        ·
          refine ⟨8790791149093503081207289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11721054865458004108276385 8790791149093503081207289)
          ·
            refine ⟨6593093361820127310905467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8790791149093503081207289 6593093361820127310905467)
            ·
              refine ⟨9889640042730190966358201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6593093361820127310905467 9889640042730190966358201)
              ·
                refine ⟨7417230032047643224768651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9889640042730190966358201 7417230032047643224768651)
                ·
                  refine ⟨11125845048071464837152977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7417230032047643224768651 11125845048071464837152977)
                  ·
                    refine ⟨8344383786053598627864733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11125845048071464837152977 8344383786053598627864733)
                    ·
                      refine ⟨3129143919770099485449275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8344383786053598627864733 3129143919770099485449275)
                      ·
                        rfl

theorem cell23_6093986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_6093986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6093986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6093986 prefixEnd_6093986 := by exact prefixLift 6093986
  have htrace : WordTrace (prefixWord ++ tailWord_6093986) baseStart_6093986 baseEnd_6093986 := by
    simpa [prefixWord, tailWord_6093986, baseEnd_6093986] using wordTrace_append hprefix tailTrace_6093986
  have hstable : (prefixWord ++ tailWord_6093986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6093986).length < 2 ^ (prefixWord ++ tailWord_6093986).sum := by decide
  have hdescent : baseEnd_6093986 < baseStart_6093986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6093986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094008 : List Nat := [2, 1, 2, 1, 2, 1, 2, 3, 1, 3, 5]
def baseStart_6094008 : Nat := 118140960795 + 6094008 * 2 ^ 59
def prefixEnd_6094008 : Nat := 4983230072969 + 3 ^ 40 * 6094008 * 2
def baseEnd_6094008 : Nat := 3129155216344498399374173

theorem tailTrace_6094008 : CollatzResearch.WordTrace tailWord_6094008 prefixEnd_6094008 3129155216344498399374173 := by
  unfold tailWord_6094008
  simp only [CollatzResearch.WordTrace]
  refine ⟨111133365853228632275641339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148177821137638176367521785 111133365853228632275641339)
  ·
    refine ⟨166700048779842948413462009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111133365853228632275641339 166700048779842948413462009)
    ·
      refine ⟨125025036584882211310096507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166700048779842948413462009 125025036584882211310096507)
      ·
        refine ⟨187537554877323316965144761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125025036584882211310096507 187537554877323316965144761)
        ·
          refine ⟨140653166157992487723858571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187537554877323316965144761 140653166157992487723858571)
          ·
            refine ⟨210979749236988731585787857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140653166157992487723858571 210979749236988731585787857)
            ·
              refine ⟨158234811927741548689340893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210979749236988731585787857 158234811927741548689340893)
              ·
                refine ⟨59338054472903080758502835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158234811927741548689340893 59338054472903080758502835)
                ·
                  refine ⟨89007081709354621137754253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59338054472903080758502835 89007081709354621137754253)
                  ·
                    refine ⟨33377655641007982926657845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89007081709354621137754253 33377655641007982926657845)
                    ·
                      refine ⟨3129155216344498399374173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33377655641007982926657845 3129155216344498399374173)
                      ·
                        rfl

theorem cell23_6094008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_6094008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094008 prefixEnd_6094008 := by exact prefixLift 6094008
  have htrace : WordTrace (prefixWord ++ tailWord_6094008) baseStart_6094008 baseEnd_6094008 := by
    simpa [prefixWord, tailWord_6094008, baseEnd_6094008] using wordTrace_append hprefix tailTrace_6094008
  have hstable : (prefixWord ++ tailWord_6094008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094008).length < 2 ^ (prefixWord ++ tailWord_6094008).sum := by decide
  have hdescent : baseEnd_6094008 < baseStart_6094008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094039 : List Nat := [1, 1, 3, 2, 1, 2, 4, 3, 2, 2, 2]
def baseStart_6094039 : Nat := 118140960795 + 6094039 * 2 ^ 59
def prefixEnd_6094039 : Nat := 4983230072969 + 3 ^ 40 * 6094039 * 2
def baseEnd_6094039 : Nat := 3129171134244787778086531

theorem tailTrace_6094039 : CollatzResearch.WordTrace tailWord_6094039 prefixEnd_6094039 3129171134244787778086531 := by
  unfold tailWord_6094039
  simp only [CollatzResearch.WordTrace]
  refine ⟨222267862369344956845661171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148178574912896637897107447 222267862369344956845661171)
  ·
    refine ⟨333401793554017435268491757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222267862369344956845661171 333401793554017435268491757)
    ·
      refine ⟨125025672582756538225684409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 333401793554017435268491757 125025672582756538225684409)
      ·
        refine ⟨93769254437067403669263307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125025672582756538225684409 93769254437067403669263307)
        ·
          refine ⟨140653881655601105503894961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93769254437067403669263307 140653881655601105503894961)
          ·
            refine ⟨105490411241700829127921221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140653881655601105503894961 105490411241700829127921221)
            ·
              refine ⟨19779452107818905461485229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105490411241700829127921221 19779452107818905461485229)
              ·
                refine ⟨7417294540432089548056961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19779452107818905461485229 7417294540432089548056961)
                ·
                  refine ⟨5562970905324067161042721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7417294540432089548056961 5562970905324067161042721)
                  ·
                    refine ⟨4172228178993050370782041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5562970905324067161042721 4172228178993050370782041)
                    ·
                      refine ⟨3129171134244787778086531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4172228178993050370782041 3129171134244787778086531)
                      ·
                        rfl

theorem cell23_6094039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 3, 2, 2, 2].length) (baseStart_6094039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094039 prefixEnd_6094039 := by exact prefixLift 6094039
  have htrace : WordTrace (prefixWord ++ tailWord_6094039) baseStart_6094039 baseEnd_6094039 := by
    simpa [prefixWord, tailWord_6094039, baseEnd_6094039] using wordTrace_append hprefix tailTrace_6094039
  have hstable : (prefixWord ++ tailWord_6094039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094039).length < 2 ^ (prefixWord ++ tailWord_6094039).sum := by decide
  have hdescent : baseEnd_6094039 < baseStart_6094039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094062 : List Nat := [4, 1, 2, 1, 1, 1, 3, 5, 5]
def baseStart_6094062 : Nat := 118140960795 + 6094062 * 2 ^ 59
def prefixEnd_6094062 : Nat := 4983230072969 + 3 ^ 40 * 6094062 * 2
def baseEnd_6094062 : Nat := 347686993811093465344325

theorem tailTrace_6094062 : CollatzResearch.WordTrace tailWord_6094062 prefixEnd_6094062 347686993811093465344325 := by
  unfold tailWord_6094062
  simp only [CollatzResearch.WordTrace]
  refine ⟨27783587656032703971718555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148179134165507754515832293 27783587656032703971718555)
  ·
    refine ⟨41675381484049055957577833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27783587656032703971718555 41675381484049055957577833)
    ·
      refine ⟨31256536113036791968183375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41675381484049055957577833 31256536113036791968183375)
      ·
        refine ⟨46884804169555187952275063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31256536113036791968183375 46884804169555187952275063)
        ·
          refine ⟨70327206254332781928412595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46884804169555187952275063 70327206254332781928412595)
          ·
            refine ⟨105490809381499172892618893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70327206254332781928412595 105490809381499172892618893)
            ·
              refine ⟨39559053518062189834732085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105490809381499172892618893 39559053518062189834732085)
              ·
                refine ⟨3708661267318330297006133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39559053518062189834732085 3708661267318330297006133)
                ·
                  refine ⟨347686993811093465344325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3708661267318330297006133 347686993811093465344325)
                  ·
                    rfl

theorem cell23_6094062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 5, 5].length) (baseStart_6094062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094062 prefixEnd_6094062 := by exact prefixLift 6094062
  have htrace : WordTrace (prefixWord ++ tailWord_6094062) baseStart_6094062 baseEnd_6094062 := by
    simpa [prefixWord, tailWord_6094062, baseEnd_6094062] using wordTrace_append hprefix tailTrace_6094062
  have hstable : (prefixWord ++ tailWord_6094062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094062).length < 2 ^ (prefixWord ++ tailWord_6094062).sum := by decide
  have hdescent : baseEnd_6094062 < baseStart_6094062 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094212 : List Nat := [2, 3, 2, 1, 1, 3, 1, 3, 1, 6]
def baseStart_6094212 : Nat := 118140960795 + 6094212 * 2 ^ 59
def prefixEnd_6094212 : Nat := 4983230072969 + 3 ^ 40 * 6094212 * 2
def baseEnd_6094212 : Nat := 1043086655466005200407745

theorem tailTrace_6094212 : CollatzResearch.WordTrace tailWord_6094212 prefixEnd_6094212 1043086655466005200407745 := by
  unfold tailWord_6094212
  simp only [CollatzResearch.WordTrace]
  refine ⟨111137086098859103695854445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148182781465145471594472593 111137086098859103695854445)
  ·
    refine ⟨41676407287072163885945417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111137086098859103695854445 41676407287072163885945417)
    ·
      refine ⟨31257305465304122914459063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41676407287072163885945417 31257305465304122914459063)
      ·
        refine ⟨46885958197956184371688595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31257305465304122914459063 46885958197956184371688595)
        ·
          refine ⟨70328937296934276557532893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46885958197956184371688595 70328937296934276557532893)
          ·
            refine ⟨26373351486350353709074835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70328937296934276557532893 26373351486350353709074835)
            ·
              refine ⟨39560027229525530563612253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26373351486350353709074835 39560027229525530563612253)
              ·
                refine ⟨14835010211072073961354595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39560027229525530563612253 14835010211072073961354595)
                ·
                  refine ⟨22252515316608110942031893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14835010211072073961354595 22252515316608110942031893)
                  ·
                    refine ⟨1043086655466005200407745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22252515316608110942031893 1043086655466005200407745)
                    ·
                      rfl

theorem cell23_6094212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_6094212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094212 prefixEnd_6094212 := by exact prefixLift 6094212
  have htrace : WordTrace (prefixWord ++ tailWord_6094212) baseStart_6094212 baseEnd_6094212 := by
    simpa [prefixWord, tailWord_6094212, baseEnd_6094212] using wordTrace_append hprefix tailTrace_6094212
  have hstable : (prefixWord ++ tailWord_6094212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094212).length < 2 ^ (prefixWord ++ tailWord_6094212).sum := by decide
  have hdescent : baseEnd_6094212 < baseStart_6094212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094242 : List Nat := [3, 3, 1, 2, 1, 3, 10]
def baseStart_6094242 : Nat := 118140960795 + 6094242 * 2 ^ 59
def prefixEnd_6094242 : Nat := 4983230072969 + 3 ^ 40 * 6094242 * 2
def baseEnd_6094242 : Nat := 38633029269353709677137

theorem tailTrace_6094242 : CollatzResearch.WordTrace tailWord_6094242 prefixEnd_6094242 38633029269353709677137 := by
  unfold tailWord_6094242
  simp only [CollatzResearch.WordTrace]
  refine ⟨55568816596902380628825245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148183510925073015010200653 55568816596902380628825245)
  ·
    refine ⟨20838306223838392735809467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55568816596902380628825245 20838306223838392735809467)
    ·
      refine ⟨31257459335757589103714201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20838306223838392735809467 31257459335757589103714201)
      ·
        refine ⟨23443094501818191827785651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31257459335757589103714201 23443094501818191827785651)
        ·
          refine ⟨35164641752727287741678477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23443094501818191827785651 35164641752727287741678477)
          ·
            refine ⟨13186740657272732903129429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35164641752727287741678477 13186740657272732903129429)
            ·
              refine ⟨38633029269353709677137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13186740657272732903129429 38633029269353709677137)
              ·
                rfl

theorem cell23_6094242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 10].length) (baseStart_6094242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094242 prefixEnd_6094242 := by exact prefixLift 6094242
  have htrace : WordTrace (prefixWord ++ tailWord_6094242) baseStart_6094242 baseEnd_6094242 := by
    simpa [prefixWord, tailWord_6094242, baseEnd_6094242] using wordTrace_append hprefix tailTrace_6094242
  have hstable : (prefixWord ++ tailWord_6094242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094242).length < 2 ^ (prefixWord ++ tailWord_6094242).sum := by decide
  have hdescent : baseEnd_6094242 < baseStart_6094242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094252 : List Nat := [2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 3]
def baseStart_6094252 : Nat := 118140960795 + 6094252 * 2 ^ 59
def prefixEnd_6094252 : Nat := 4983230072969 + 3 ^ 40 * 6094252 * 2
def baseEnd_6094252 : Nat := 3129280505624195444723051

theorem tailTrace_6094252 : CollatzResearch.WordTrace tailWord_6094252 prefixEnd_6094252 3129280505624195444723051 := by
  unfold tailWord_6094252
  simp only [CollatzResearch.WordTrace]
  refine ⟨111137815558786647111582505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148183754078382196148776673 111137815558786647111582505)
  ·
    refine ⟨83353361669089985333686879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111137815558786647111582505 83353361669089985333686879)
    ·
      refine ⟨125030042503634978000530319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83353361669089985333686879 125030042503634978000530319)
      ·
        refine ⟨187545063755452467000795479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125030042503634978000530319 187545063755452467000795479)
        ·
          refine ⟨281317595633178700501193219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187545063755452467000795479 281317595633178700501193219)
          ·
            refine ⟨421976393449768050751789829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281317595633178700501193219 421976393449768050751789829)
            ·
              refine ⟨79120573771831509515960593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 421976393449768050751789829 79120573771831509515960593)
              ·
                refine ⟨59340430328873632136970445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79120573771831509515960593 59340430328873632136970445)
                ·
                  refine ⟨22252661373327612051363917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59340430328873632136970445 22252661373327612051363917)
                  ·
                    refine ⟨8344748014997854519261469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22252661373327612051363917 8344748014997854519261469)
                    ·
                      refine ⟨3129280505624195444723051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8344748014997854519261469 3129280505624195444723051)
                      ·
                        rfl

theorem cell23_6094252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 3].length) (baseStart_6094252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094252 prefixEnd_6094252 := by exact prefixLift 6094252
  have htrace : WordTrace (prefixWord ++ tailWord_6094252) baseStart_6094252 baseEnd_6094252 := by
    simpa [prefixWord, tailWord_6094252, baseEnd_6094252] using wordTrace_append hprefix tailTrace_6094252
  have hstable : (prefixWord ++ tailWord_6094252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094252).length < 2 ^ (prefixWord ++ tailWord_6094252).sum := by decide
  have hdescent : baseEnd_6094252 < baseStart_6094252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094253 : List Nat := [1, 5, 2, 2, 1, 1, 1, 3, 3, 2, 2]
def baseStart_6094253 : Nat := 118140960795 + 6094253 * 2 ^ 59
def prefixEnd_6094253 : Nat := 4983230072969 + 3 ^ 40 * 6094253 * 2
def baseEnd_6094253 : Nat := 3129281019104849940810547

theorem tailTrace_6094253 : CollatzResearch.WordTrace tailWord_6094253 prefixEnd_6094253 3129281019104849940810547 := by
  unfold tailWord_6094253
  simp only [CollatzResearch.WordTrace]
  refine ⟨222275667590569671393951413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148183778393713114262634275 222275667590569671393951413)
  ·
    refine ⟨20838343836615906693182945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 222275667590569671393951413 20838343836615906693182945)
    ·
      refine ⟨15628757877461930019887209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20838343836615906693182945 15628757877461930019887209)
      ·
        refine ⟨11721568408096447514915407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15628757877461930019887209 11721568408096447514915407)
        ·
          refine ⟨17582352612144671272373111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11721568408096447514915407 17582352612144671272373111)
          ·
            refine ⟨26373528918217006908559667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17582352612144671272373111 26373528918217006908559667)
            ·
              refine ⟨39560293377325510362839501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26373528918217006908559667 39560293377325510362839501)
              ·
                refine ⟨14835110016497066386064813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39560293377325510362839501 14835110016497066386064813)
                ·
                  refine ⟨5563166256186399894774305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14835110016497066386064813 5563166256186399894774305)
                  ·
                    refine ⟨4172374692139799921080729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5563166256186399894774305 4172374692139799921080729)
                    ·
                      refine ⟨3129281019104849940810547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4172374692139799921080729 3129281019104849940810547)
                      ·
                        rfl

theorem cell23_6094253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_6094253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094253 prefixEnd_6094253 := by exact prefixLift 6094253
  have htrace : WordTrace (prefixWord ++ tailWord_6094253) baseStart_6094253 baseEnd_6094253 := by
    simpa [prefixWord, tailWord_6094253, baseEnd_6094253] using wordTrace_append hprefix tailTrace_6094253
  have hstable : (prefixWord ++ tailWord_6094253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094253).length < 2 ^ (prefixWord ++ tailWord_6094253).sum := by decide
  have hdescent : baseEnd_6094253 < baseStart_6094253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094255 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 1, 9]
def baseStart_6094255 : Nat := 118140960795 + 6094255 * 2 ^ 59
def prefixEnd_6094255 : Nat := 4983230072969 + 3 ^ 40 * 6094255 * 2
def baseEnd_6094255 : Nat := 1043094015355386310995179

theorem tailTrace_6094255 : CollatzResearch.WordTrace tailWord_6094255 prefixEnd_6094255 1043094015355386310995179 := by
  unfold tailWord_6094255
  simp only [CollatzResearch.WordTrace]
  refine ⟨222275740536562425735524219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148183827024374950490349479 222275740536562425735524219)
  ·
    refine ⟨333413610804843638603286329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222275740536562425735524219 333413610804843638603286329)
    ·
      refine ⟨250060208103632728952464747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333413610804843638603286329 250060208103632728952464747)
      ·
        refine ⟨375090312155449093428697121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250060208103632728952464747 375090312155449093428697121)
        ·
          refine ⟨281317734116586820071522841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 375090312155449093428697121 281317734116586820071522841)
          ·
            refine ⟨210988300587440115053642131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281317734116586820071522841 210988300587440115053642131)
            ·
              refine ⟨316482450881160172580463197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210988300587440115053642131 316482450881160172580463197)
              ·
                refine ⟨118680919080435064717673699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 316482450881160172580463197 118680919080435064717673699)
                ·
                  refine ⟨178021378620652597076510549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118680919080435064717673699 178021378620652597076510549)
                  ·
                    refine ⟨1043094015355386310995179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 178021378620652597076510549 1043094015355386310995179)
                    ·
                      rfl

theorem cell23_6094255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 9].length) (baseStart_6094255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094255 prefixEnd_6094255 := by exact prefixLift 6094255
  have htrace : WordTrace (prefixWord ++ tailWord_6094255) baseStart_6094255 baseEnd_6094255 := by
    simpa [prefixWord, tailWord_6094255, baseEnd_6094255] using wordTrace_append hprefix tailTrace_6094255
  have hstable : (prefixWord ++ tailWord_6094255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094255).length < 2 ^ (prefixWord ++ tailWord_6094255).sum := by decide
  have hdescent : baseEnd_6094255 < baseStart_6094255 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094276 : List Nat := [2, 3, 3, 2, 1, 3, 2, 7]
def baseStart_6094276 : Nat := 118140960795 + 6094276 * 2 ^ 59
def prefixEnd_6094276 : Nat := 4983230072969 + 3 ^ 40 * 6094276 * 2
def baseEnd_6094276 : Nat := 115899734413329753734183

theorem tailTrace_6094276 : CollatzResearch.WordTrace tailWord_6094276 prefixEnd_6094276 115899734413329753734183 := by
  unfold tailWord_6094276
  simp only [CollatzResearch.WordTrace]
  refine ⟨111138253234743173161019341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148184337646324230881359121 111138253234743173161019341)
  ·
    refine ⟨41676844963028689935382253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111138253234743173161019341 41676844963028689935382253)
    ·
      refine ⟨15628816861135758725768345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41676844963028689935382253 15628816861135758725768345)
      ·
        refine ⟨11721612645851819044326259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15628816861135758725768345 11721612645851819044326259)
        ·
          refine ⟨17582418968777728566489389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11721612645851819044326259 17582418968777728566489389)
          ·
            refine ⟨6593407113291648212433521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17582418968777728566489389 6593407113291648212433521)
            ·
              refine ⟨4945055334968736159325141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6593407113291648212433521 4945055334968736159325141)
              ·
                refine ⟨115899734413329753734183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4945055334968736159325141 115899734413329753734183)
                ·
                  rfl

theorem cell23_6094276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 7].length) (baseStart_6094276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094276 prefixEnd_6094276 := by exact prefixLift 6094276
  have htrace : WordTrace (prefixWord ++ tailWord_6094276) baseStart_6094276 baseEnd_6094276 := by
    simpa [prefixWord, tailWord_6094276, baseEnd_6094276] using wordTrace_append hprefix tailTrace_6094276
  have hstable : (prefixWord ++ tailWord_6094276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094276).length < 2 ^ (prefixWord ++ tailWord_6094276).sum := by decide
  have hdescent : baseEnd_6094276 < baseStart_6094276 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094282 : List Nat := [3, 1, 2, 1, 2, 3, 1, 1, 2, 2, 5]
def baseStart_6094282 : Nat := 118140960795 + 6094282 * 2 ^ 59
def prefixEnd_6094282 : Nat := 4983230072969 + 3 ^ 40 * 6094282 * 2
def baseEnd_6094282 : Nat := 3129295910043830327347913

theorem tailTrace_6094282 : CollatzResearch.WordTrace tailWord_6094282 prefixEnd_6094282 3129295910043830327347913 := by
  unfold tailWord_6094282
  simp only [CollatzResearch.WordTrace]
  refine ⟨55569181326866152336689275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148184483538309739564504733 55569181326866152336689275)
  ·
    refine ⟨83353771990299228505033913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55569181326866152336689275 83353771990299228505033913)
    ·
      refine ⟨62515328992724421378775435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83353771990299228505033913 62515328992724421378775435)
      ·
        refine ⟨93772993489086632068163153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62515328992724421378775435 93772993489086632068163153)
        ·
          refine ⟨70329745116814974051122365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93772993489086632068163153 70329745116814974051122365)
          ·
            refine ⟨26373654418805615269170887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70329745116814974051122365 26373654418805615269170887)
            ·
              refine ⟨39560481628208422903756331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26373654418805615269170887 39560481628208422903756331)
              ·
                refine ⟨59340722442312634355634497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39560481628208422903756331 59340722442312634355634497)
                ·
                  refine ⟨44505541831734475766725873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59340722442312634355634497 44505541831734475766725873)
                  ·
                    refine ⟨33379156373800856825044405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44505541831734475766725873 33379156373800856825044405)
                    ·
                      refine ⟨3129295910043830327347913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33379156373800856825044405 3129295910043830327347913)
                      ·
                        rfl

theorem cell23_6094282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_6094282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094282 prefixEnd_6094282 := by exact prefixLift 6094282
  have htrace : WordTrace (prefixWord ++ tailWord_6094282) baseStart_6094282 baseEnd_6094282 := by
    simpa [prefixWord, tailWord_6094282, baseEnd_6094282] using wordTrace_append hprefix tailTrace_6094282
  have hstable : (prefixWord ++ tailWord_6094282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094282).length < 2 ^ (prefixWord ++ tailWord_6094282).sum := by decide
  have hdescent : baseEnd_6094282 < baseStart_6094282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094296 : List Nat := [2, 1, 2, 2, 2, 1, 4, 3, 1, 3, 2]
def baseStart_6094296 : Nat := 118140960795 + 6094296 * 2 ^ 59
def prefixEnd_6094296 : Nat := 4983230072969 + 3 ^ 40 * 6094296 * 2
def baseEnd_6094296 : Nat := 3129303098772993272572849

theorem tailTrace_6094296 : CollatzResearch.WordTrace tailWord_6094296 prefixEnd_6094296 3129303098772993272572849 := by
  unfold tailWord_6094296
  simp only [CollatzResearch.WordTrace]
  refine ⟨111138617964706944868883371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148184823952942593158511161 111138617964706944868883371)
  ·
    refine ⟨166707926947060417303325057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111138617964706944868883371 166707926947060417303325057)
    ·
      refine ⟨125030945210295312977493793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166707926947060417303325057 125030945210295312977493793)
      ·
        refine ⟨93773208907721484733120345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125030945210295312977493793 93773208907721484733120345)
        ·
          refine ⟨70329906680791113549840259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93773208907721484733120345 70329906680791113549840259)
          ·
            refine ⟨105494860021186670324760389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70329906680791113549840259 105494860021186670324760389)
            ·
              refine ⟨19780286253972500685892573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105494860021186670324760389 19780286253972500685892573)
              ·
                refine ⟨7417607345239687757209715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19780286253972500685892573 7417607345239687757209715)
                ·
                  refine ⟨11126411017859531635814573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7417607345239687757209715 11126411017859531635814573)
                  ·
                    refine ⟨4172404131697324363430465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11126411017859531635814573 4172404131697324363430465)
                    ·
                      refine ⟨3129303098772993272572849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4172404131697324363430465 3129303098772993272572849)
                      ·
                        rfl

theorem cell23_6094296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 3, 1, 3, 2].length) (baseStart_6094296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094296 prefixEnd_6094296 := by exact prefixLift 6094296
  have htrace : WordTrace (prefixWord ++ tailWord_6094296) baseStart_6094296 baseEnd_6094296 := by
    simpa [prefixWord, tailWord_6094296, baseEnd_6094296] using wordTrace_append hprefix tailTrace_6094296
  have hstable : (prefixWord ++ tailWord_6094296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094296).length < 2 ^ (prefixWord ++ tailWord_6094296).sum := by decide
  have hdescent : baseEnd_6094296 < baseStart_6094296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094312 : List Nat := [2, 1, 4, 1, 1, 2, 1, 2, 1, 3, 5]
def baseStart_6094312 : Nat := 118140960795 + 6094312 * 2 ^ 59
def prefixEnd_6094312 : Nat := 4983230072969 + 3 ^ 40 * 6094312 * 2
def baseEnd_6094312 : Nat := 3129311314463465209972775

theorem tailTrace_6094312 : CollatzResearch.WordTrace tailWord_6094312 prefixEnd_6094312 3129311314463465209972775 := by
  unfold tailWord_6094312
  simp only [CollatzResearch.WordTrace]
  refine ⟨111138909748677962235174595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148185212998237282980232793 111138909748677962235174595)
  ·
    refine ⟨166708364623016943352761893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111138909748677962235174595 166708364623016943352761893)
    ·
      refine ⟨31257818366815676878642855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166708364623016943352761893 31257818366815676878642855)
      ·
        refine ⟨46886727550223515317964283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31257818366815676878642855 46886727550223515317964283)
        ·
          refine ⟨70330091325335272976946425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46886727550223515317964283 70330091325335272976946425)
          ·
            refine ⟨52747568494001454732709819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70330091325335272976946425 52747568494001454732709819)
            ·
              refine ⟨79121352741002182099064729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52747568494001454732709819 79121352741002182099064729)
              ·
                refine ⟨59341014555751636574298547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79121352741002182099064729 59341014555751636574298547)
                ·
                  refine ⟨89011521833627454861447821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59341014555751636574298547 89011521833627454861447821)
                  ·
                    refine ⟨33379320687610295573042933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89011521833627454861447821 33379320687610295573042933)
                    ·
                      refine ⟨3129311314463465209972775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33379320687610295573042933 3129311314463465209972775)
                      ·
                        rfl

theorem cell23_6094312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_6094312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094312 prefixEnd_6094312 := by exact prefixLift 6094312
  have htrace : WordTrace (prefixWord ++ tailWord_6094312) baseStart_6094312 baseEnd_6094312 := by
    simpa [prefixWord, tailWord_6094312, baseEnd_6094312] using wordTrace_append hprefix tailTrace_6094312
  have hstable : (prefixWord ++ tailWord_6094312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094312).length < 2 ^ (prefixWord ++ tailWord_6094312).sum := by decide
  have hdescent : baseEnd_6094312 < baseStart_6094312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094332 : List Nat := [2, 2, 2, 1, 2, 1, 2, 4, 7]
def baseStart_6094332 : Nat := 118140960795 + 6094332 * 2 ^ 59
def prefixEnd_6094332 : Nat := 4983230072969 + 3 ^ 40 * 6094332 * 2
def baseEnd_6094332 : Nat := 347702398230728347969187

theorem tailTrace_6094332 : CollatzResearch.WordTrace tailWord_6094332 prefixEnd_6094332 347702398230728347969187 := by
  unfold tailWord_6094332
  simp only [CollatzResearch.WordTrace]
  refine ⟨111139274478641733943038625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148185699304855645257384833 111139274478641733943038625)
  ·
    refine ⟨83354455858981300457278969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111139274478641733943038625 83354455858981300457278969)
    ·
      refine ⟨62515841894235975342959227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83354455858981300457278969 62515841894235975342959227)
      ·
        refine ⟨93773762841353963014438841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62515841894235975342959227 93773762841353963014438841)
        ·
          refine ⟨70330322131015472260829131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93773762841353963014438841 70330322131015472260829131)
          ·
            refine ⟨105495483196523208391243697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70330322131015472260829131 105495483196523208391243697)
            ·
              refine ⟨79121612397392406293432773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105495483196523208391243697 79121612397392406293432773)
              ·
                refine ⟨14835302324511076180018645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79121612397392406293432773 14835302324511076180018645)
                ·
                  refine ⟨347702398230728347969187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14835302324511076180018645 347702398230728347969187)
                  ·
                    rfl

theorem cell23_6094332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 7].length) (baseStart_6094332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094332 prefixEnd_6094332 := by exact prefixLift 6094332
  have htrace : WordTrace (prefixWord ++ tailWord_6094332) baseStart_6094332 baseEnd_6094332 := by
    simpa [prefixWord, tailWord_6094332, baseEnd_6094332] using wordTrace_append hprefix tailTrace_6094332
  have hstable : (prefixWord ++ tailWord_6094332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094332).length < 2 ^ (prefixWord ++ tailWord_6094332).sum := by decide
  have hdescent : baseEnd_6094332 < baseStart_6094332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094360 : List Nat := [2, 1, 2, 3, 4, 1, 2, 2, 2, 2, 2]
def baseStart_6094360 : Nat := 118140960795 + 6094360 * 2 ^ 59
def prefixEnd_6094360 : Nat := 4983230072969 + 3 ^ 40 * 6094360 * 2
def baseEnd_6094360 : Nat := 3129335961534881022172555

theorem tailTrace_6094360 : CollatzResearch.WordTrace tailWord_6094360 prefixEnd_6094360 3129335961534881022172555 := by
  unfold tailWord_6094360
  simp only [CollatzResearch.WordTrace]
  refine ⟨111139785100591014334048267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148186380134121352445397689 111139785100591014334048267)
  ·
    refine ⟨166709677650886521501072401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111139785100591014334048267 166709677650886521501072401)
    ·
      refine ⟨125032258238164891125804301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166709677650886521501072401 125032258238164891125804301)
      ·
        refine ⟨46887096839311834172176613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125032258238164891125804301 46887096839311834172176613)
        ·
          refine ⟨8791330657370968907283115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46887096839311834172176613 8791330657370968907283115)
          ·
            refine ⟨13186995986056453360924673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8791330657370968907283115 13186995986056453360924673)
            ·
              refine ⟨9890246989542340020693505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13186995986056453360924673 9890246989542340020693505)
              ·
                refine ⟨7417685242156755015520129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9890246989542340020693505 7417685242156755015520129)
                ·
                  refine ⟨5563263931617566261640097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7417685242156755015520129 5563263931617566261640097)
                  ·
                    refine ⟨4172447948713174696230073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5563263931617566261640097 4172447948713174696230073)
                    ·
                      refine ⟨3129335961534881022172555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4172447948713174696230073 3129335961534881022172555)
                      ·
                        rfl

theorem cell23_6094360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 2, 2, 2, 2].length) (baseStart_6094360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094360 prefixEnd_6094360 := by exact prefixLift 6094360
  have htrace : WordTrace (prefixWord ++ tailWord_6094360) baseStart_6094360 baseEnd_6094360 := by
    simpa [prefixWord, tailWord_6094360, baseEnd_6094360] using wordTrace_append hprefix tailTrace_6094360
  have hstable : (prefixWord ++ tailWord_6094360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094360).length < 2 ^ (prefixWord ++ tailWord_6094360).sum := by decide
  have hdescent : baseEnd_6094360 < baseStart_6094360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094362 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 3, 7]
def baseStart_6094362 : Nat := 118140960795 + 6094362 * 2 ^ 59
def prefixEnd_6094362 : Nat := 4983230072969 + 3 ^ 40 * 6094362 * 2
def baseEnd_6094362 : Nat := 1043112329498730004782515

theorem tailTrace_6094362 : CollatzResearch.WordTrace tailWord_6094362 prefixEnd_6094362 1043112329498730004782515 := by
  unfold tailWord_6094362
  simp only [CollatzResearch.WordTrace]
  refine ⟨55569910786793695752417335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148186428764783188673112893 55569910786793695752417335)
  ·
    refine ⟨83354866180190543628626003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55569910786793695752417335 83354866180190543628626003)
    ·
      refine ⟨125032299270285815442939005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83354866180190543628626003 125032299270285815442939005)
      ·
        refine ⟨46887112226357180791102127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125032299270285815442939005 46887112226357180791102127)
        ·
          refine ⟨70330668339535771186653191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46887112226357180791102127 70330668339535771186653191)
          ·
            refine ⟨105496002509303656779979787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70330668339535771186653191 105496002509303656779979787)
            ·
              refine ⟨158244003763955485169969681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105496002509303656779979787 158244003763955485169969681)
              ·
                refine ⟨118683002822966613877477261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158244003763955485169969681 118683002822966613877477261)
                ·
                  refine ⟨44506126058612480204053973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118683002822966613877477261 44506126058612480204053973)
                  ·
                    refine ⟨1043112329498730004782515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44506126058612480204053973 1043112329498730004782515)
                    ·
                      rfl

theorem cell23_6094362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 3, 7].length) (baseStart_6094362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094362 prefixEnd_6094362 := by exact prefixLift 6094362
  have htrace : WordTrace (prefixWord ++ tailWord_6094362) baseStart_6094362 baseEnd_6094362 := by
    simpa [prefixWord, tailWord_6094362, baseEnd_6094362] using wordTrace_append hprefix tailTrace_6094362
  have hstable : (prefixWord ++ tailWord_6094362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094362).length < 2 ^ (prefixWord ++ tailWord_6094362).sum := by decide
  have hdescent : baseEnd_6094362 < baseStart_6094362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094399 : List Nat := [1, 1, 2, 2, 3, 4, 1, 1, 1, 3, 4]
def baseStart_6094399 : Nat := 118140960795 + 6094399 * 2 ^ 59
def prefixEnd_6094399 : Nat := 4983230072969 + 3 ^ 40 * 6094399 * 2
def baseEnd_6094399 : Nat := 3129355987280406369584875

theorem tailTrace_6094399 : CollatzResearch.WordTrace tailWord_6094399 prefixEnd_6094399 3129355987280406369584875 := by
  unfold tailWord_6094399
  simp only [CollatzResearch.WordTrace]
  refine ⟨222280992648040738328766251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148187328432027158885844167 222280992648040738328766251)
  ·
    refine ⟨333421488972061107493149377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222280992648040738328766251 333421488972061107493149377)
    ·
      refine ⟨250066116729045830619862033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333421488972061107493149377 250066116729045830619862033)
      ·
        refine ⟨187549587546784372964896525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250066116729045830619862033 187549587546784372964896525)
        ·
          refine ⟨70331095330044139861836197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187549587546784372964896525 70331095330044139861836197)
          ·
            refine ⟨13187080374383276224094287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70331095330044139861836197 13187080374383276224094287)
            ·
              refine ⟨19780620561574914336141431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13187080374383276224094287 19780620561574914336141431)
              ·
                refine ⟨29670930842362371504212147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19780620561574914336141431 29670930842362371504212147)
                ·
                  refine ⟨44506396263543557256318221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29670930842362371504212147 44506396263543557256318221)
                  ·
                    refine ⟨16689898598828833971119333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44506396263543557256318221 16689898598828833971119333)
                    ·
                      refine ⟨3129355987280406369584875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16689898598828833971119333 3129355987280406369584875)
                      ·
                        rfl

theorem cell23_6094399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 3, 4].length) (baseStart_6094399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094399 prefixEnd_6094399 := by exact prefixLift 6094399
  have htrace : WordTrace (prefixWord ++ tailWord_6094399) baseStart_6094399 baseEnd_6094399 := by
    simpa [prefixWord, tailWord_6094399, baseEnd_6094399] using wordTrace_append hprefix tailTrace_6094399
  have hstable : (prefixWord ++ tailWord_6094399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094399).length < 2 ^ (prefixWord ++ tailWord_6094399).sum := by decide
  have hdescent : baseEnd_6094399 < baseStart_6094399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094439 : List Nat := [1, 1, 5, 1, 1, 1, 2, 5, 6]
def baseStart_6094439 : Nat := 118140960795 + 6094439 * 2 ^ 59
def prefixEnd_6094439 : Nat := 4983230072969 + 3 ^ 40 * 6094439 * 2
def baseEnd_6094439 : Nat := 347708502945176245898299

theorem tailTrace_6094439 : CollatzResearch.WordTrace tailWord_6094439 prefixEnd_6094439 347708502945176245898299 := by
  unfold tailWord_6094439
  simp only [CollatzResearch.WordTrace]
  refine ⟨222282451567895825160222371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148188301045263883440148247 222282451567895825160222371)
  ·
    refine ⟨333423677351843737740333557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222282451567895825160222371 333423677351843737740333557)
    ·
      refine ⟨31258469751735350413156271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 333423677351843737740333557 31258469751735350413156271)
      ·
        refine ⟨46887704627603025619734407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31258469751735350413156271 46887704627603025619734407)
        ·
          refine ⟨70331556941404538429601611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46887704627603025619734407 70331556941404538429601611)
          ·
            refine ⟨105497335412106807644402417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70331556941404538429601611 105497335412106807644402417)
            ·
              refine ⟨79123001559080105733301813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105497335412106807644402417 79123001559080105733301813)
              ·
                refine ⟨7417781396163759912497045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79123001559080105733301813 7417781396163759912497045)
                ·
                  refine ⟨347708502945176245898299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7417781396163759912497045 347708502945176245898299)
                  ·
                    rfl

theorem cell23_6094439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 5, 6].length) (baseStart_6094439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094439 prefixEnd_6094439 := by exact prefixLift 6094439
  have htrace : WordTrace (prefixWord ++ tailWord_6094439) baseStart_6094439 baseEnd_6094439 := by
    simpa [prefixWord, tailWord_6094439, baseEnd_6094439] using wordTrace_append hprefix tailTrace_6094439
  have hstable : (prefixWord ++ tailWord_6094439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094439).length < 2 ^ (prefixWord ++ tailWord_6094439).sum := by decide
  have hdescent : baseEnd_6094439 < baseStart_6094439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094499 : List Nat := [1, 1, 1, 4, 1, 1, 4, 3, 1, 6]
def baseStart_6094499 : Nat := 118140960795 + 6094499 * 2 ^ 59
def prefixEnd_6094499 : Nat := 4983230072969 + 3 ^ 40 * 6094499 * 2
def baseEnd_6094499 : Nat := 1043135778448618659444805

theorem tailTrace_6094499 : CollatzResearch.WordTrace tailWord_6094499 prefixEnd_6094499 1043135778448618659444805 := by
  unfold tailWord_6094499
  simp only [CollatzResearch.WordTrace]
  refine ⟨222284639947678455407406551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148189759965118970271604367 222284639947678455407406551)
  ·
    refine ⟨333426959921517683111109827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222284639947678455407406551 333426959921517683111109827)
    ·
      refine ⟨500140439882276524666664741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333426959921517683111109827 500140439882276524666664741)
      ·
        refine ⟨93776332477926848374999639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 500140439882276524666664741 93776332477926848374999639)
        ·
          refine ⟨140664498716890272562499459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93776332477926848374999639 140664498716890272562499459)
          ·
            refine ⟨210996748075335408843749189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140664498716890272562499459 210996748075335408843749189)
            ·
              refine ⟨39561890264125389158202973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 210996748075335408843749189 39561890264125389158202973)
              ·
                refine ⟨14835708849047020934326115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39561890264125389158202973 14835708849047020934326115)
                ·
                  refine ⟨22253563273570531401489173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14835708849047020934326115 22253563273570531401489173)
                  ·
                    refine ⟨1043135778448618659444805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22253563273570531401489173 1043135778448618659444805)
                    ·
                      rfl

theorem cell23_6094499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 6].length) (baseStart_6094499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094499 prefixEnd_6094499 := by exact prefixLift 6094499
  have htrace : WordTrace (prefixWord ++ tailWord_6094499) baseStart_6094499 baseEnd_6094499 := by
    simpa [prefixWord, tailWord_6094499, baseEnd_6094499] using wordTrace_append hprefix tailTrace_6094499
  have hstable : (prefixWord ++ tailWord_6094499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094499).length < 2 ^ (prefixWord ++ tailWord_6094499).sum := by decide
  have hdescent : baseEnd_6094499 < baseStart_6094499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094529 : List Nat := [1, 2, 6, 14]
def baseStart_6094529 : Nat := 118140960795 + 6094529 * 2 ^ 59
def prefixEnd_6094529 : Nat := 4983230072969 + 3 ^ 40 * 6094529 * 2
def baseEnd_6094529 : Nat := 1430920319965930892071

theorem tailTrace_6094529 : CollatzResearch.WordTrace tailWord_6094529 prefixEnd_6094529 1430920319965930892071 := by
  unfold tailWord_6094529
  simp only [CollatzResearch.WordTrace]
  refine ⟨222285734137569770530998641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148190489425046513687332427 222285734137569770530998641)
  ·
    refine ⟨166714300603177327898248981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222285734137569770530998641 166714300603177327898248981)
    ·
      refine ⟨7814732840773937245230421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 166714300603177327898248981 7814732840773937245230421)
      ·
        refine ⟨1430920319965930892071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 7814732840773937245230421 1430920319965930892071)
        ·
          rfl

theorem cell23_6094529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 14].length) (baseStart_6094529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094529 prefixEnd_6094529 := by exact prefixLift 6094529
  have htrace : WordTrace (prefixWord ++ tailWord_6094529) baseStart_6094529 baseEnd_6094529 := by
    simpa [prefixWord, tailWord_6094529, baseEnd_6094529] using wordTrace_append hprefix tailTrace_6094529
  have hstable : (prefixWord ++ tailWord_6094529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094529).length < 2 ^ (prefixWord ++ tailWord_6094529).sum := by decide
  have hdescent : baseEnd_6094529 < baseStart_6094529 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094546 : List Nat := [3, 2, 2, 2, 2, 1, 3, 8]
def baseStart_6094546 : Nat := 118140960795 + 6094546 * 2 ^ 59
def prefixEnd_6094546 : Nat := 4983230072969 + 3 ^ 40 * 6094546 * 2
def baseEnd_6094546 : Nat := 115904869219874714609137

theorem tailTrace_6094546 : CollatzResearch.WordTrace tailWord_6094546 prefixEnd_6094546 115904869219874714609137 := by
  unfold tailWord_6094546
  simp only [CollatzResearch.WordTrace]
  refine ⟨55571588544627045608591873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148190902785672121622911661 55571588544627045608591873)
  ·
    refine ⟨41678691408470284206443905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55571588544627045608591873 41678691408470284206443905)
    ·
      refine ⟨31259018556352713154832929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41678691408470284206443905 31259018556352713154832929)
      ·
        refine ⟨23444263917264534866124697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31259018556352713154832929 23444263917264534866124697)
        ·
          refine ⟨17583197937948401149593523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23444263917264534866124697 17583197937948401149593523)
          ·
            refine ⟨26374796906922601724390285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17583197937948401149593523 26374796906922601724390285)
            ·
              refine ⟨9890548840095975646646357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26374796906922601724390285 9890548840095975646646357)
              ·
                refine ⟨115904869219874714609137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9890548840095975646646357 115904869219874714609137)
                ·
                  rfl

theorem cell23_6094546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 8].length) (baseStart_6094546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094546 prefixEnd_6094546 := by exact prefixLift 6094546
  have htrace : WordTrace (prefixWord ++ tailWord_6094546) baseStart_6094546 baseEnd_6094546 := by
    simpa [prefixWord, tailWord_6094546, baseEnd_6094546] using wordTrace_append hprefix tailTrace_6094546
  have hstable : (prefixWord ++ tailWord_6094546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094546).length < 2 ^ (prefixWord ++ tailWord_6094546).sum := by decide
  have hdescent : baseEnd_6094546 < baseStart_6094546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094559 : List Nat := [1, 1, 2, 3, 2, 2, 1, 2, 2, 7]
def baseStart_6094559 : Nat := 118140960795 + 6094559 * 2 ^ 59
def prefixEnd_6094559 : Nat := 4983230072969 + 3 ^ 40 * 6094559 * 2
def baseEnd_6094559 : Nat := 1043146048061708581194713

theorem tailTrace_6094559 : CollatzResearch.WordTrace tailWord_6094559 prefixEnd_6094559 1043146048061708581194713 := by
  unfold tailWord_6094559
  simp only [CollatzResearch.WordTrace]
  refine ⟨222286828327461085654590731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148191218884974057103060487 222286828327461085654590731)
  ·
    refine ⟨333430242491191628481886097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222286828327461085654590731 333430242491191628481886097)
    ·
      refine ⟨250072681868393721361414573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333430242491191628481886097 250072681868393721361414573)
      ·
        refine ⟨93777255700647645510530465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250072681868393721361414573 93777255700647645510530465)
        ·
          refine ⟨70332941775485734132897849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93777255700647645510530465 70332941775485734132897849)
          ·
            refine ⟨52749706331614300599673387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70332941775485734132897849 52749706331614300599673387)
            ·
              refine ⟨79124559497421450899510081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52749706331614300599673387 79124559497421450899510081)
              ·
                refine ⟨59343419623066088174632561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79124559497421450899510081 59343419623066088174632561)
                ·
                  refine ⟨44507564717299566130974421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59343419623066088174632561 44507564717299566130974421)
                  ·
                    refine ⟨1043146048061708581194713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44507564717299566130974421 1043146048061708581194713)
                    ·
                      rfl

theorem cell23_6094559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 7].length) (baseStart_6094559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094559 prefixEnd_6094559 := by exact prefixLift 6094559
  have htrace : WordTrace (prefixWord ++ tailWord_6094559) baseStart_6094559 baseEnd_6094559 := by
    simpa [prefixWord, tailWord_6094559, baseEnd_6094559] using wordTrace_append hprefix tailTrace_6094559
  have hstable : (prefixWord ++ tailWord_6094559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094559).length < 2 ^ (prefixWord ++ tailWord_6094559).sum := by decide
  have hdescent : baseEnd_6094559 < baseStart_6094559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094563 : List Nat := [1, 1, 1, 7, 2, 1, 3, 7]
def baseStart_6094563 : Nat := 118140960795 + 6094563 * 2 ^ 59
def prefixEnd_6094563 : Nat := 4983230072969 + 3 ^ 40 * 6094563 * 2
def baseEnd_6094563 : Nat := 115905192522509026960523

theorem tailTrace_6094563 : CollatzResearch.WordTrace tailWord_6094563 prefixEnd_6094563 115905192522509026960523 := by
  unfold tailWord_6094563
  simp only [CollatzResearch.WordTrace]
  refine ⟨222286974219446594337736343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148191316146297729558490895 222286974219446594337736343)
  ·
    refine ⟨333430461329169891506604515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222286974219446594337736343 333430461329169891506604515)
    ·
      refine ⟨500145691993754837259906773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333430461329169891506604515 500145691993754837259906773)
      ·
        refine ⟨11722164656103628998279065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 500145691993754837259906773 11722164656103628998279065)
        ·
          refine ⟨8791623492077721748709299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11722164656103628998279065 8791623492077721748709299)
          ·
            refine ⟨13187435238116582623063949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8791623492077721748709299 13187435238116582623063949)
            ·
              refine ⟨4945288214293718483648981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13187435238116582623063949 4945288214293718483648981)
              ·
                refine ⟨115905192522509026960523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4945288214293718483648981 115905192522509026960523)
                ·
                  rfl

theorem cell23_6094563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 7].length) (baseStart_6094563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094563 prefixEnd_6094563 := by exact prefixLift 6094563
  have htrace : WordTrace (prefixWord ++ tailWord_6094563) baseStart_6094563 baseEnd_6094563 := by
    simpa [prefixWord, tailWord_6094563, baseEnd_6094563] using wordTrace_append hprefix tailTrace_6094563
  have hstable : (prefixWord ++ tailWord_6094563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094563).length < 2 ^ (prefixWord ++ tailWord_6094563).sum := by decide
  have hdescent : baseEnd_6094563 < baseStart_6094563 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094569 : List Nat := [1, 2, 1, 1, 1, 2, 3, 3, 2, 2, 5]
def baseStart_6094569 : Nat := 118140960795 + 6094569 * 2 ^ 59
def prefixEnd_6094569 : Nat := 4983230072969 + 3 ^ 40 * 6094569 * 2
def baseEnd_6094569 : Nat := 3129443278991670704459093

theorem tailTrace_6094569 : CollatzResearch.WordTrace tailWord_6094569 prefixEnd_6094569 3129443278991670704459093 := by
  unfold tailWord_6094569
  simp only [CollatzResearch.WordTrace]
  refine ⟨222287193057424857362454761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148191462038283238241636507 222287193057424857362454761)
  ·
    refine ⟨166715394793068643021841071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222287193057424857362454761 166715394793068643021841071)
    ·
      refine ⟨250073092189602964532761607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166715394793068643021841071 250073092189602964532761607)
      ·
        refine ⟨375109638284404446799142411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250073092189602964532761607 375109638284404446799142411)
        ·
          refine ⟨562664457426606670198713617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375109638284404446799142411 562664457426606670198713617)
          ·
            refine ⟨421998343069955002649035213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 562664457426606670198713617 421998343069955002649035213)
            ·
              refine ⟨158249378651233125993388205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 421998343069955002649035213 158249378651233125993388205)
              ·
                refine ⟨59343516994212422247520577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158249378651233125993388205 59343516994212422247520577)
                ·
                  refine ⟨44507637745659316685640433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59343516994212422247520577 44507637745659316685640433)
                  ·
                    refine ⟨33380728309244487514230325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44507637745659316685640433 33380728309244487514230325)
                    ·
                      refine ⟨3129443278991670704459093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33380728309244487514230325 3129443278991670704459093)
                      ·
                        rfl

theorem cell23_6094569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 2, 5].length) (baseStart_6094569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094569 prefixEnd_6094569 := by exact prefixLift 6094569
  have htrace : WordTrace (prefixWord ++ tailWord_6094569) baseStart_6094569 baseEnd_6094569 := by
    simpa [prefixWord, tailWord_6094569, baseEnd_6094569] using wordTrace_append hprefix tailTrace_6094569
  have hstable : (prefixWord ++ tailWord_6094569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094569).length < 2 ^ (prefixWord ++ tailWord_6094569).sum := by decide
  have hdescent : baseEnd_6094569 < baseStart_6094569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094573 : List Nat := [1, 5, 1, 2, 1, 2, 2, 2, 1, 3, 3]
def baseStart_6094573 : Nat := 118140960795 + 6094573 * 2 ^ 59
def prefixEnd_6094573 : Nat := 4983230072969 + 3 ^ 40 * 6094573 * 2
def baseEnd_6094573 : Nat := 3129445332914288688809075

theorem tailTrace_6094573 : CollatzResearch.WordTrace tailWord_6094573 prefixEnd_6094573 3129445332914288688809075 := by
  unfold tailWord_6094573
  simp only [CollatzResearch.WordTrace]
  refine ⟨222287338949410366045600373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148191559299606910697066915 222287338949410366045600373)
  ·
    refine ⟨20839438026507221816775035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 222287338949410366045600373 20839438026507221816775035)
    ·
      refine ⟨31259157039760832725162553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20839438026507221816775035 31259157039760832725162553)
      ·
        refine ⟨23444367779820624543871915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31259157039760832725162553 23444367779820624543871915)
        ·
          refine ⟨35166551669730936815807873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23444367779820624543871915 35166551669730936815807873)
          ·
            refine ⟨26374913752298202611855905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35166551669730936815807873 26374913752298202611855905)
            ·
              refine ⟨19781185314223651958891929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26374913752298202611855905 19781185314223651958891929)
              ·
                refine ⟨14835888985667738969168947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19781185314223651958891929 14835888985667738969168947)
                ·
                  refine ⟨22253833478501608453753421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14835888985667738969168947 22253833478501608453753421)
                  ·
                    refine ⟨8345187554438103170157533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22253833478501608453753421 8345187554438103170157533)
                    ·
                      refine ⟨3129445332914288688809075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8345187554438103170157533 3129445332914288688809075)
                      ·
                        rfl

theorem cell23_6094573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_6094573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094573 prefixEnd_6094573 := by exact prefixLift 6094573
  have htrace : WordTrace (prefixWord ++ tailWord_6094573) baseStart_6094573 baseEnd_6094573 := by
    simpa [prefixWord, tailWord_6094573, baseEnd_6094573] using wordTrace_append hprefix tailTrace_6094573
  have hstable : (prefixWord ++ tailWord_6094573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094573).length < 2 ^ (prefixWord ++ tailWord_6094573).sum := by decide
  have hdescent : baseEnd_6094573 < baseStart_6094573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094606 : List Nat := [4, 1, 1, 2, 1, 1, 4, 1, 2, 6]
def baseStart_6094606 : Nat := 118140960795 + 6094606 * 2 ^ 59
def prefixEnd_6094606 : Nat := 4983230072969 + 3 ^ 40 * 6094606 * 2
def baseEnd_6094606 : Nat := 1043154092591962353232141

theorem tailTrace_6094606 : CollatzResearch.WordTrace tailWord_6094606 prefixEnd_6094606 1043154092591962353232141 := by
  unfold tailWord_6094606
  simp only [CollatzResearch.WordTrace]
  refine ⟨27786067819786351585193959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148192361705527208454367781 27786067819786351585193959)
  ·
    refine ⟨41679101729679527377790939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27786067819786351585193959 41679101729679527377790939)
    ·
      refine ⟨62518652594519291066686409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41679101729679527377790939 62518652594519291066686409)
      ·
        refine ⟨46888989445889468300014807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62518652594519291066686409 46888989445889468300014807)
        ·
          refine ⟨70333484168834202450022211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46888989445889468300014807 70333484168834202450022211)
          ·
            refine ⟨105500226253251303675033317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70333484168834202450022211 105500226253251303675033317)
            ·
              refine ⟨19781292422484619439068747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105500226253251303675033317 19781292422484619439068747)
              ·
                refine ⟨29671938633726929158603121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19781292422484619439068747 29671938633726929158603121)
                ·
                  refine ⟨22253953975295196868952341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29671938633726929158603121 22253953975295196868952341)
                  ·
                    refine ⟨1043154092591962353232141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22253953975295196868952341 1043154092591962353232141)
                    ·
                      rfl

theorem cell23_6094606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_6094606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094606 prefixEnd_6094606 := by exact prefixLift 6094606
  have htrace : WordTrace (prefixWord ++ tailWord_6094606) baseStart_6094606 baseEnd_6094606 := by
    simpa [prefixWord, tailWord_6094606, baseEnd_6094606] using wordTrace_append hprefix tailTrace_6094606
  have hstable : (prefixWord ++ tailWord_6094606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094606).length < 2 ^ (prefixWord ++ tailWord_6094606).sum := by decide
  have hdescent : baseEnd_6094606 < baseStart_6094606 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094616 : List Nat := [2, 1, 2, 3, 1, 1, 2, 2, 2, 4, 3]
def baseStart_6094616 : Nat := 118140960795 + 6094616 * 2 ^ 59
def prefixEnd_6094616 : Nat := 4983230072969 + 3 ^ 40 * 6094616 * 2
def baseEnd_6094616 : Nat := 3129467412582432020571377

theorem tailTrace_6094616 : CollatzResearch.WordTrace tailWord_6094616 prefixEnd_6094616 3129467412582432020571377 := by
  unfold tailWord_6094616
  simp only [CollatzResearch.WordTrace]
  refine ⟨111144453644127292194707851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148192604858836389592943801 111144453644127292194707851)
  ·
    refine ⟨166716680466190938292061777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111144453644127292194707851 166716680466190938292061777)
    ·
      refine ⟨125037510349643203719046333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166716680466190938292061777 125037510349643203719046333)
      ·
        refine ⟨46889066381116201394642375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125037510349643203719046333 46889066381116201394642375)
        ·
          refine ⟨70333599571674302091963563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46889066381116201394642375 70333599571674302091963563)
          ·
            refine ⟨105500399357511453137945345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70333599571674302091963563 105500399357511453137945345)
            ·
              refine ⟨79125299518133589853459009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105500399357511453137945345 79125299518133589853459009)
              ·
                refine ⟨59343974638600192390094257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79125299518133589853459009 59343974638600192390094257)
                ·
                  refine ⟨44507980978950144292570693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59343974638600192390094257 44507980978950144292570693)
                  ·
                    refine ⟨8345246433553152054857005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44507980978950144292570693 8345246433553152054857005)
                    ·
                      refine ⟨3129467412582432020571377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8345246433553152054857005 3129467412582432020571377)
                      ·
                        rfl

theorem cell23_6094616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_6094616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094616 prefixEnd_6094616 := by exact prefixLift 6094616
  have htrace : WordTrace (prefixWord ++ tailWord_6094616) baseStart_6094616 baseEnd_6094616 := by
    simpa [prefixWord, tailWord_6094616, baseEnd_6094616] using wordTrace_append hprefix tailTrace_6094616
  have hstable : (prefixWord ++ tailWord_6094616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094616).length < 2 ^ (prefixWord ++ tailWord_6094616).sum := by decide
  have hdescent : baseEnd_6094616 < baseStart_6094616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094653 : List Nat := [1, 4, 1, 4, 1, 1, 3, 1, 7]
def baseStart_6094653 : Nat := 118140960795 + 6094653 * 2 ^ 59
def prefixEnd_6094653 : Nat := 4983230072969 + 3 ^ 40 * 6094653 * 2
def baseEnd_6094653 : Nat := 347720712374072041756523

theorem tailTrace_6094653 : CollatzResearch.WordTrace tailWord_6094653 prefixEnd_6094653 347720712374072041756523 := by
  unfold tailWord_6094653
  simp only [CollatzResearch.WordTrace]
  refine ⟨222290256789120539708512613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148193504526080359805675075 222290256789120539708512613)
  ·
    refine ⟨41679423147960101195346115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222290256789120539708512613 41679423147960101195346115)
    ·
      refine ⟨62519134721940151793019173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41679423147960101195346115 62519134721940151793019173)
      ·
        refine ⟨11722337760363778461191095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62519134721940151793019173 11722337760363778461191095)
        ·
          refine ⟨17583506640545667691786643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11722337760363778461191095 17583506640545667691786643)
          ·
            refine ⟨26375259960818501537679965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17583506640545667691786643 26375259960818501537679965)
            ·
              refine ⟨9890722485306938076629987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26375259960818501537679965 9890722485306938076629987)
              ·
                refine ⟨14836083727960407114944981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9890722485306938076629987 14836083727960407114944981)
                ·
                  refine ⟨347720712374072041756523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14836083727960407114944981 347720712374072041756523)
                  ·
                    rfl

theorem cell23_6094653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 7].length) (baseStart_6094653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094653 prefixEnd_6094653 := by exact prefixLift 6094653
  have htrace : WordTrace (prefixWord ++ tailWord_6094653) baseStart_6094653 baseEnd_6094653 := by
    simpa [prefixWord, tailWord_6094653, baseEnd_6094653] using wordTrace_append hprefix tailTrace_6094653
  have hstable : (prefixWord ++ tailWord_6094653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094653).length < 2 ^ (prefixWord ++ tailWord_6094653).sum := by decide
  have hdescent : baseEnd_6094653 < baseStart_6094653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094664 : List Nat := [2, 1, 3, 1, 1, 6, 2, 1, 2, 2, 2]
def baseStart_6094664 : Nat := 118140960795 + 6094664 * 2 ^ 59
def prefixEnd_6094664 : Nat := 4983230072969 + 3 ^ 40 * 6094664 * 2
def baseEnd_6094664 : Nat := 3129492059653847832771157

theorem tailTrace_6094664 : CollatzResearch.WordTrace tailWord_6094664 prefixEnd_6094664 3129492059653847832771157 := by
  unfold tailWord_6094664
  simp only [CollatzResearch.WordTrace]
  refine ⟨111145328996040344293581523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148193771994720459058108697 111145328996040344293581523)
  ·
    refine ⟨166717993494060516440372285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111145328996040344293581523 166717993494060516440372285)
    ·
      refine ⟨62519247560272693665139607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166717993494060516440372285 62519247560272693665139607)
      ·
        refine ⟨93778871340409040497709411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62519247560272693665139607 93778871340409040497709411)
        ·
          refine ⟨140668307010613560746564117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93778871340409040497709411 140668307010613560746564117)
          ·
            refine ⟨6593826891122510659995193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 140668307010613560746564117 6593826891122510659995193)
            ·
              refine ⟨4945370168341882994996395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6593826891122510659995193 4945370168341882994996395)
              ·
                refine ⟨7418055252512824492494593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4945370168341882994996395 7418055252512824492494593)
                ·
                  refine ⟨5563541439384618369370945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7418055252512824492494593 5563541439384618369370945)
                  ·
                    refine ⟨4172656079538463777028209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5563541439384618369370945 4172656079538463777028209)
                    ·
                      refine ⟨3129492059653847832771157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4172656079538463777028209 3129492059653847832771157)
                      ·
                        rfl

theorem cell23_6094664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 1, 2, 2, 2].length) (baseStart_6094664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094664 prefixEnd_6094664 := by exact prefixLift 6094664
  have htrace : WordTrace (prefixWord ++ tailWord_6094664) baseStart_6094664 baseEnd_6094664 := by
    simpa [prefixWord, tailWord_6094664, baseEnd_6094664] using wordTrace_append hprefix tailTrace_6094664
  have hstable : (prefixWord ++ tailWord_6094664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094664).length < 2 ^ (prefixWord ++ tailWord_6094664).sum := by decide
  have hdescent : baseEnd_6094664 < baseStart_6094664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094666 : List Nat := [3, 1, 2, 1, 1, 1, 3, 2, 4, 5]
def baseStart_6094666 : Nat := 118140960795 + 6094666 * 2 ^ 59
def prefixEnd_6094666 : Nat := 4983230072969 + 3 ^ 40 * 6094666 * 2
def baseEnd_6094666 : Nat := 1043164362205052274982049

theorem tailTrace_6094666 : CollatzResearch.WordTrace tailWord_6094666 prefixEnd_6094666 1043164362205052274982049 := by
  unfold tailWord_6094666
  simp only [CollatzResearch.WordTrace]
  refine ⟨55572682734518360732183963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148193820625382295285823901 55572682734518360732183963)
  ·
    refine ⟨83359024101777541098275945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55572682734518360732183963 83359024101777541098275945)
    ·
      refine ⟨62519268076333155823706959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83359024101777541098275945 62519268076333155823706959)
      ·
        refine ⟨93778902114499733735560439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62519268076333155823706959 93778902114499733735560439)
        ·
          refine ⟨140668353171749600603340659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93778902114499733735560439 140668353171749600603340659)
          ·
            refine ⟨211002529757624400905010989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140668353171749600603340659 211002529757624400905010989)
            ·
              refine ⟨79125948659109150339379121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 211002529757624400905010989 79125948659109150339379121)
              ·
                refine ⟨59344461494331862754534341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79125948659109150339379121 59344461494331862754534341)
                ·
                  refine ⟨11127086530187224266475189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59344461494331862754534341 11127086530187224266475189)
                  ·
                    refine ⟨1043164362205052274982049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11127086530187224266475189 1043164362205052274982049)
                    ·
                      rfl

theorem cell23_6094666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_6094666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094666 prefixEnd_6094666 := by exact prefixLift 6094666
  have htrace : WordTrace (prefixWord ++ tailWord_6094666) baseStart_6094666 baseEnd_6094666 := by
    simpa [prefixWord, tailWord_6094666, baseEnd_6094666] using wordTrace_append hprefix tailTrace_6094666
  have hstable : (prefixWord ++ tailWord_6094666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094666).length < 2 ^ (prefixWord ++ tailWord_6094666).sum := by decide
  have hdescent : baseEnd_6094666 < baseStart_6094666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094706 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 1, 5, 5]
def baseStart_6094706 : Nat := 118140960795 + 6094706 * 2 ^ 59
def prefixEnd_6094706 : Nat := 4983230072969 + 3 ^ 40 * 6094706 * 2
def baseEnd_6094706 : Nat := 3129513625841336668445963

theorem tailTrace_6094706 : CollatzResearch.WordTrace tailWord_6094706 prefixEnd_6094706 3129513625841336668445963 := by
  unfold tailWord_6094706
  simp only [CollatzResearch.WordTrace]
  refine ⟨55573047464482132440047993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148194793238619019840127981 55573047464482132440047993)
  ·
    refine ⟨41679785598361599330035995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55573047464482132440047993 41679785598361599330035995)
    ·
      refine ⟨62519678397542398995053993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41679785598361599330035995 62519678397542398995053993)
      ·
        refine ⟨46889758798156799246290495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62519678397542398995053993 46889758798156799246290495)
        ·
          refine ⟨70334638197235198869435743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46889758798156799246290495 70334638197235198869435743)
          ·
            refine ⟨105501957295852798304153615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70334638197235198869435743 105501957295852798304153615)
            ·
              refine ⟨158252935943779197456230423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105501957295852798304153615 158252935943779197456230423)
              ·
                refine ⟨237379403915668796184345635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158252935943779197456230423 237379403915668796184345635)
                ·
                  refine ⟨356069105873503194276518453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 237379403915668796184345635 356069105873503194276518453)
                  ·
                    refine ⟨33381478675640924463423605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 356069105873503194276518453 33381478675640924463423605)
                    ·
                      refine ⟨3129513625841336668445963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33381478675640924463423605 3129513625841336668445963)
                      ·
                        rfl

theorem cell23_6094706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_6094706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094706 prefixEnd_6094706 := by exact prefixLift 6094706
  have htrace : WordTrace (prefixWord ++ tailWord_6094706) baseStart_6094706 baseEnd_6094706 := by
    simpa [prefixWord, tailWord_6094706, baseEnd_6094706] using wordTrace_append hprefix tailTrace_6094706
  have hstable : (prefixWord ++ tailWord_6094706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094706).length < 2 ^ (prefixWord ++ tailWord_6094706).sum := by decide
  have hdescent : baseEnd_6094706 < baseStart_6094706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094713 : List Nat := [1, 2, 1, 3, 2, 2, 2, 3, 3, 4]
def baseStart_6094713 : Nat := 118140960795 + 6094713 * 2 ^ 59
def prefixEnd_6094713 : Nat := 4983230072969 + 3 ^ 40 * 6094713 * 2
def baseEnd_6094713 : Nat := 1043172406735306047019477

theorem tailTrace_6094713 : CollatzResearch.WordTrace tailWord_6094713 prefixEnd_6094713 1043172406735306047019477 := by
  unfold tailWord_6094713
  simp only [CollatzResearch.WordTrace]
  refine ⟨222292445168903169955696793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148194963445935446637131195 222292445168903169955696793)
  ·
    refine ⟨166719333876677377466772595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222292445168903169955696793 166719333876677377466772595)
    ·
      refine ⟨250079000815016066200158893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166719333876677377466772595 250079000815016066200158893)
      ·
        refine ⟨93779625305631024825059585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250079000815016066200158893 93779625305631024825059585)
        ·
          refine ⟨70334718979223268618794689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93779625305631024825059585 70334718979223268618794689)
          ·
            refine ⟨52751039234417451464096017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70334718979223268618794689 52751039234417451464096017)
            ·
              refine ⟨39563279425813088598072013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52751039234417451464096017 39563279425813088598072013)
              ·
                refine ⟨14836229784679908224277005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39563279425813088598072013 14836229784679908224277005)
                ·
                  refine ⟨5563586169254965584103877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14836229784679908224277005 5563586169254965584103877)
                  ·
                    refine ⟨1043172406735306047019477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5563586169254965584103877 1043172406735306047019477)
                    ·
                      rfl

theorem cell23_6094713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 3, 4].length) (baseStart_6094713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094713 prefixEnd_6094713 := by exact prefixLift 6094713
  have htrace : WordTrace (prefixWord ++ tailWord_6094713) baseStart_6094713 baseEnd_6094713 := by
    simpa [prefixWord, tailWord_6094713, baseEnd_6094713] using wordTrace_append hprefix tailTrace_6094713
  have hstable : (prefixWord ++ tailWord_6094713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094713).length < 2 ^ (prefixWord ++ tailWord_6094713).sum := by decide
  have hdescent : baseEnd_6094713 < baseStart_6094713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094716 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 4, 4, 4]
def baseStart_6094716 : Nat := 118140960795 + 6094716 * 2 ^ 59
def prefixEnd_6094716 : Nat := 4983230072969 + 3 ^ 40 * 6094716 * 2
def baseEnd_6094716 : Nat := 3129518760647881629320917

theorem tailTrace_6094716 : CollatzResearch.WordTrace tailWord_6094716 prefixEnd_6094716 3129518760647881629320917 := by
  unfold tailWord_6094716
  simp only [CollatzResearch.WordTrace]
  refine ⟨111146277293946150734028001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148195036391928200978704001 111146277293946150734028001)
  ·
    refine ⟨83359707970459613050521001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111146277293946150734028001 83359707970459613050521001)
    ·
      refine ⟨62519780977844709787890751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83359707970459613050521001 62519780977844709787890751)
      ·
        refine ⟨93779671466767064681836127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62519780977844709787890751 93779671466767064681836127)
        ·
          refine ⟨140669507200150597022754191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93779671466767064681836127 140669507200150597022754191)
          ·
            refine ⟨211004260800225895534131287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140669507200150597022754191 211004260800225895534131287)
            ·
              refine ⟨316506391200338843301196931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211004260800225895534131287 316506391200338843301196931)
              ·
                refine ⟨474759586800508264951795397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 316506391200338843301196931 474759586800508264951795397)
                ·
                  refine ⟨89017422525095299678461637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 474759586800508264951795397 89017422525095299678461637)
                  ·
                    refine ⟨16690766723455368689711557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 89017422525095299678461637 16690766723455368689711557)
                    ·
                      refine ⟨3129518760647881629320917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16690766723455368689711557 3129518760647881629320917)
                      ·
                        rfl

theorem cell23_6094716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_6094716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094716 prefixEnd_6094716 := by exact prefixLift 6094716
  have htrace : WordTrace (prefixWord ++ tailWord_6094716) baseStart_6094716 baseEnd_6094716 := by
    simpa [prefixWord, tailWord_6094716, baseEnd_6094716] using wordTrace_append hprefix tailTrace_6094716
  have hstable : (prefixWord ++ tailWord_6094716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094716).length < 2 ^ (prefixWord ++ tailWord_6094716).sum := by decide
  have hdescent : baseEnd_6094716 < baseStart_6094716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094734 : List Nat := [4, 1, 1, 5, 2, 1, 1, 1, 2, 5]
def baseStart_6094734 : Nat := 118140960795 + 6094734 * 2 ^ 59
def prefixEnd_6094734 : Nat := 4983230072969 + 3 ^ 40 * 6094734 * 2
def baseEnd_6094734 : Nat := 1043176001099887519631945

theorem tailTrace_6094734 : CollatzResearch.WordTrace tailWord_6094734 prefixEnd_6094734 1043176001099887519631945 := by
  unfold tailWord_6094734
  simp only [CollatzResearch.WordTrace]
  refine ⟨27786651387728386317776407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148195474067884727028140837 27786651387728386317776407)
  ·
    refine ⟨41679977081592579476664611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27786651387728386317776407 41679977081592579476664611)
    ·
      refine ⟨62519965622388869214996917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41679977081592579476664611 62519965622388869214996917)
      ·
        refine ⟨5861246777098956488905961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62519965622388869214996917 5861246777098956488905961)
        ·
          refine ⟨4395935082824217366679471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5861246777098956488905961 4395935082824217366679471)
          ·
            refine ⟨6593902624236326050019207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4395935082824217366679471 6593902624236326050019207)
            ·
              refine ⟨9890853936354489075028811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6593902624236326050019207 9890853936354489075028811)
              ·
                refine ⟨14836280904531733612543217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9890853936354489075028811 14836280904531733612543217)
                ·
                  refine ⟨11127210678398800209407413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14836280904531733612543217 11127210678398800209407413)
                  ·
                    refine ⟨1043176001099887519631945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11127210678398800209407413 1043176001099887519631945)
                    ·
                      rfl

theorem cell23_6094734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 2, 5].length) (baseStart_6094734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094734 prefixEnd_6094734 := by exact prefixLift 6094734
  have htrace : WordTrace (prefixWord ++ tailWord_6094734) baseStart_6094734 baseEnd_6094734 := by
    simpa [prefixWord, tailWord_6094734, baseEnd_6094734] using wordTrace_append hprefix tailTrace_6094734
  have hstable : (prefixWord ++ tailWord_6094734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094734).length < 2 ^ (prefixWord ++ tailWord_6094734).sum := by decide
  have hdescent : baseEnd_6094734 < baseStart_6094734 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094740 : List Nat := [2, 4, 2, 1, 1, 3, 1, 1, 1, 4, 3]
def baseStart_6094740 : Nat := 118140960795 + 6094740 * 2 ^ 59
def prefixEnd_6094740 : Nat := 4983230072969 + 3 ^ 40 * 6094740 * 2
def baseEnd_6094740 : Nat := 3129531084183589535420807

theorem tailTrace_6094740 : CollatzResearch.WordTrace tailWord_6094740 prefixEnd_6094740 3129531084183589535420807 := by
  unfold tailWord_6094740
  simp only [CollatzResearch.WordTrace]
  refine ⟨111146714969902676783464837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148195619959870235711286449 111146714969902676783464837)
  ·
    refine ⟨20840009056856751896899657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111146714969902676783464837 20840009056856751896899657)
    ·
      refine ⟨15630006792642563922674743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20840009056856751896899657 15630006792642563922674743)
      ·
        refine ⟨23445010188963845884012115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15630006792642563922674743 23445010188963845884012115)
        ·
          refine ⟨35167515283445768826018173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23445010188963845884012115 35167515283445768826018173)
          ·
            refine ⟨13187818231292163309756815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35167515283445768826018173 13187818231292163309756815)
            ·
              refine ⟨19781727346938244964635223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13187818231292163309756815 19781727346938244964635223)
              ·
                refine ⟨29672591020407367446952835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19781727346938244964635223 29672591020407367446952835)
                ·
                  refine ⟨44508886530611051170429253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29672591020407367446952835 44508886530611051170429253)
                  ·
                    refine ⟨8345416224489572094455485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44508886530611051170429253 8345416224489572094455485)
                    ·
                      refine ⟨3129531084183589535420807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8345416224489572094455485 3129531084183589535420807)
                      ·
                        rfl

theorem cell23_6094740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_6094740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094740 prefixEnd_6094740 := by exact prefixLift 6094740
  have htrace : WordTrace (prefixWord ++ tailWord_6094740) baseStart_6094740 baseEnd_6094740 := by
    simpa [prefixWord, tailWord_6094740, baseEnd_6094740] using wordTrace_append hprefix tailTrace_6094740
  have hstable : (prefixWord ++ tailWord_6094740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094740).length < 2 ^ (prefixWord ++ tailWord_6094740).sum := by decide
  have hdescent : baseEnd_6094740 < baseStart_6094740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094763 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 5, 5, 2]
def baseStart_6094763 : Nat := 118140960795 + 6094763 * 2 ^ 59
def prefixEnd_6094763 : Nat := 4983230072969 + 3 ^ 40 * 6094763 * 2
def baseEnd_6094763 : Nat := 3129542894238642945433201

theorem tailTrace_6094763 : CollatzResearch.WordTrace tailWord_6094763 prefixEnd_6094763 3129542894238642945433201 := by
  unfold tailWord_6094763
  simp only [CollatzResearch.WordTrace]
  refine ⟨222294268818722028495016943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148196179212481352330011295 222294268818722028495016943)
  ·
    refine ⟨333441403228083042742525415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222294268818722028495016943 333441403228083042742525415)
    ·
      refine ⟨500162104842124564113788123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333441403228083042742525415 500162104842124564113788123)
      ·
        refine ⟨750243157263186846170682185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500162104842124564113788123 750243157263186846170682185)
        ·
          refine ⟨562682367947390134628011639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 750243157263186846170682185 562682367947390134628011639)
          ·
            refine ⟨844023551921085201942017459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 562682367947390134628011639 844023551921085201942017459)
            ·
              refine ⟨1266035327881627802913026189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 844023551921085201942017459 1266035327881627802913026189)
              ·
                refine ⟨474763247955610426092384821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1266035327881627802913026189 474763247955610426092384821)
                ·
                  refine ⟨44509054495838477446161077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 474763247955610426092384821 44509054495838477446161077)
                  ·
                    refine ⟨4172723858984857260577601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44509054495838477446161077 4172723858984857260577601)
                    ·
                      refine ⟨3129542894238642945433201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4172723858984857260577601 3129542894238642945433201)
                      ·
                        rfl

theorem cell23_6094763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 5, 2].length) (baseStart_6094763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094763 prefixEnd_6094763 := by exact prefixLift 6094763
  have htrace : WordTrace (prefixWord ++ tailWord_6094763) baseStart_6094763 baseEnd_6094763 := by
    simpa [prefixWord, tailWord_6094763, baseEnd_6094763] using wordTrace_append hprefix tailTrace_6094763
  have hstable : (prefixWord ++ tailWord_6094763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094763).length < 2 ^ (prefixWord ++ tailWord_6094763).sum := by decide
  have hdescent : baseEnd_6094763 < baseStart_6094763 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094820 : List Nat := [2, 3, 1, 1, 1, 1, 4, 4, 2, 4]
def baseStart_6094820 : Nat := 118140960795 + 6094820 * 2 ^ 59
def prefixEnd_6094820 : Nat := 4983230072969 + 3 ^ 40 * 6094820 * 2
def baseEnd_6094820 : Nat := 1043190720878649740806813

theorem tailTrace_6094820 : CollatzResearch.WordTrace tailWord_6094820 prefixEnd_6094820 1043190720878649740806813 := by
  unfold tailWord_6094820
  simp only [CollatzResearch.WordTrace]
  refine ⟨111148173889757763614920957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148197565186343684819894609 111148173889757763614920957)
  ·
    refine ⟨41680565208659161355595359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111148173889757763614920957 41680565208659161355595359)
    ·
      refine ⟨62520847812988742033393039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41680565208659161355595359 62520847812988742033393039)
      ·
        refine ⟨93781271719483113050089559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62520847812988742033393039 93781271719483113050089559)
        ·
          refine ⟨140671907579224669575134339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93781271719483113050089559 140671907579224669575134339)
          ·
            refine ⟨211007861368837004362701509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140671907579224669575134339 211007861368837004362701509)
            ·
              refine ⟨39563974006656938318006533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 211007861368837004362701509 39563974006656938318006533)
              ·
                refine ⟨7418245126248175934626225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39563974006656938318006533 7418245126248175934626225)
                ·
                  refine ⟨5563683844686131950969669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7418245126248175934626225 5563683844686131950969669)
                  ·
                    refine ⟨1043190720878649740806813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5563683844686131950969669 1043190720878649740806813)
                    ·
                      rfl

theorem cell23_6094820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 4, 2, 4].length) (baseStart_6094820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094820 prefixEnd_6094820 := by exact prefixLift 6094820
  have htrace : WordTrace (prefixWord ++ tailWord_6094820) baseStart_6094820 baseEnd_6094820 := by
    simpa [prefixWord, tailWord_6094820, baseEnd_6094820] using wordTrace_append hprefix tailTrace_6094820
  have hstable : (prefixWord ++ tailWord_6094820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094820).length < 2 ^ (prefixWord ++ tailWord_6094820).sum := by decide
  have hdescent : baseEnd_6094820 < baseStart_6094820 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094830 : List Nat := [4, 1, 2, 1, 3, 1, 2, 2, 1, 1, 5]
def baseStart_6094830 : Nat := 118140960795 + 6094830 * 2 ^ 59
def prefixEnd_6094830 : Nat := 4983230072969 + 3 ^ 40 * 6094830 * 2
def baseEnd_6094830 : Nat := 3129577297442494183295393

theorem tailTrace_6094830 : CollatzResearch.WordTrace tailWord_6094830 prefixEnd_6094830 3129577297442494183295393 := by
  unfold tailWord_6094830
  simp only [CollatzResearch.WordTrace]
  refine ⟨27787089063684912367213243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148197808339652865958470629 27787089063684912367213243)
  ·
    refine ⟨41680633595527368550819865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27787089063684912367213243 41680633595527368550819865)
    ·
      refine ⟨31260475196645526413114899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41680633595527368550819865 31260475196645526413114899)
      ·
        refine ⟨46890712794968289619672349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31260475196645526413114899 46890712794968289619672349)
        ·
          refine ⟨17584017298113108607377131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46890712794968289619672349 17584017298113108607377131)
          ·
            refine ⟨26376025947169662911065697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17584017298113108607377131 26376025947169662911065697)
            ·
              refine ⟨19782019460377247183299273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26376025947169662911065697 19782019460377247183299273)
              ·
                refine ⟨14836514595282935387474455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19782019460377247183299273 14836514595282935387474455)
                ·
                  refine ⟨22254771892924403081211683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14836514595282935387474455 22254771892924403081211683)
                  ·
                    refine ⟨33382157839386604621817525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22254771892924403081211683 33382157839386604621817525)
                    ·
                      refine ⟨3129577297442494183295393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33382157839386604621817525 3129577297442494183295393)
                      ·
                        rfl

theorem cell23_6094830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_6094830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094830 prefixEnd_6094830 := by exact prefixLift 6094830
  have htrace : WordTrace (prefixWord ++ tailWord_6094830) baseStart_6094830 baseEnd_6094830 := by
    simpa [prefixWord, tailWord_6094830, baseEnd_6094830] using wordTrace_append hprefix tailTrace_6094830
  have hstable : (prefixWord ++ tailWord_6094830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094830).length < 2 ^ (prefixWord ++ tailWord_6094830).sum := by decide
  have hdescent : baseEnd_6094830 < baseStart_6094830 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094860 : List Nat := [2, 2, 1, 2, 3, 1, 3, 2, 1, 3, 3]
def baseStart_6094860 : Nat := 118140960795 + 6094860 * 2 ^ 59
def prefixEnd_6094860 : Nat := 4983230072969 + 3 ^ 40 * 6094860 * 2
def baseEnd_6094860 : Nat := 3129592701862129065920255

theorem tailTrace_6094860 : CollatzResearch.WordTrace tailWord_6094860 prefixEnd_6094860 3129592701862129065920255 := by
  unfold tailWord_6094860
  simp only [CollatzResearch.WordTrace]
  refine ⟨111148903349685307030649017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148198537799580409374198689 111148903349685307030649017)
  ·
    refine ⟨83361677512263980272986763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111148903349685307030649017 83361677512263980272986763)
    ·
      refine ⟨125042516268395970409480145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83361677512263980272986763 125042516268395970409480145)
      ·
        refine ⟨93781887201296977807110109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125042516268395970409480145 93781887201296977807110109)
        ·
          refine ⟨35168207700486366677666291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93781887201296977807110109 35168207700486366677666291)
          ·
            refine ⟨52752311550729550016499437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35168207700486366677666291 52752311550729550016499437)
            ·
              refine ⟨19782116831523581256187289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52752311550729550016499437 19782116831523581256187289)
              ·
                refine ⟨14836587623642685942140467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19782116831523581256187289 14836587623642685942140467)
                ·
                  refine ⟨22254881435464028913210701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14836587623642685942140467 22254881435464028913210701)
                  ·
                    refine ⟨8345580538299010842454013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22254881435464028913210701 8345580538299010842454013)
                    ·
                      refine ⟨3129592701862129065920255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8345580538299010842454013 3129592701862129065920255)
                      ·
                        rfl

theorem cell23_6094860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 1, 3, 3].length) (baseStart_6094860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094860 prefixEnd_6094860 := by exact prefixLift 6094860
  have htrace : WordTrace (prefixWord ++ tailWord_6094860) baseStart_6094860 baseEnd_6094860 := by
    simpa [prefixWord, tailWord_6094860, baseEnd_6094860] using wordTrace_append hprefix tailTrace_6094860
  have hstable : (prefixWord ++ tailWord_6094860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094860).length < 2 ^ (prefixWord ++ tailWord_6094860).sum := by decide
  have hdescent : baseEnd_6094860 < baseStart_6094860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094883 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 1, 5, 4]
def baseStart_6094883 : Nat := 118140960795 + 6094883 * 2 ^ 59
def prefixEnd_6094883 : Nat := 4983230072969 + 3 ^ 40 * 6094883 * 2
def baseEnd_6094883 : Nat := 3129604511917182475932649

theorem tailTrace_6094883 : CollatzResearch.WordTrace tailWord_6094883 prefixEnd_6094883 3129604511917182475932649 := by
  unfold tailWord_6094883
  simp only [CollatzResearch.WordTrace]
  refine ⟨222298645578287288989385303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148199097052191525992923535 222298645578287288989385303)
  ·
    refine ⟨333447968367430933484077955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222298645578287288989385303 333447968367430933484077955)
    ·
      refine ⟨500171952551146400226116933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333447968367430933484077955 500171952551146400226116933)
      ·
        refine ⟨93782241103339950042396925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 500171952551146400226116933 93782241103339950042396925)
        ·
          refine ⟨35168340413752481265898847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93782241103339950042396925 35168340413752481265898847)
          ·
            refine ⟨52752510620628721898848271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35168340413752481265898847 52752510620628721898848271)
            ·
              refine ⟨79128765930943082848272407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52752510620628721898848271 79128765930943082848272407)
              ·
                refine ⟨118693148896414624272408611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79128765930943082848272407 118693148896414624272408611)
                ·
                  refine ⟨178039723344621936408612917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118693148896414624272408611 178039723344621936408612917)
                  ·
                    refine ⟨16691224063558306538307461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 178039723344621936408612917 16691224063558306538307461)
                    ·
                      refine ⟨3129604511917182475932649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16691224063558306538307461 3129604511917182475932649)
                      ·
                        rfl

theorem cell23_6094883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_6094883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094883 prefixEnd_6094883 := by exact prefixLift 6094883
  have htrace : WordTrace (prefixWord ++ tailWord_6094883) baseStart_6094883 baseEnd_6094883 := by
    simpa [prefixWord, tailWord_6094883, baseEnd_6094883] using wordTrace_append hprefix tailTrace_6094883
  have hstable : (prefixWord ++ tailWord_6094883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094883).length < 2 ^ (prefixWord ++ tailWord_6094883).sum := by decide
  have hdescent : baseEnd_6094883 < baseStart_6094883 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094894 : List Nat := [4, 1, 3, 1, 1, 2, 2, 3, 2, 1, 3]
def baseStart_6094894 : Nat := 118140960795 + 6094894 * 2 ^ 59
def prefixEnd_6094894 : Nat := 4983230072969 + 3 ^ 40 * 6094894 * 2
def baseEnd_6094894 : Nat := 3129610160204381932895099

theorem tailTrace_6094894 : CollatzResearch.WordTrace tailWord_6094894 prefixEnd_6094894 3129610160204381932895099 := by
  unfold tailWord_6094894
  simp only [CollatzResearch.WordTrace]
  refine ⟨27787380847655929733504467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148199364520831625245357157 27787380847655929733504467)
  ·
    refine ⟨41681071271483894600256701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27787380847655929733504467 41681071271483894600256701)
    ·
      refine ⟨15630401726806460475096263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41681071271483894600256701 15630401726806460475096263)
      ·
        refine ⟨23445602590209690712644395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15630401726806460475096263 23445602590209690712644395)
        ·
          refine ⟨35168403885314536068966593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23445602590209690712644395 35168403885314536068966593)
          ·
            refine ⟨26376302913985902051724945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35168403885314536068966593 26376302913985902051724945)
            ·
              refine ⟨19782227185489426538793709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26376302913985902051724945 19782227185489426538793709)
              ·
                refine ⟨7418335194558534952047641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19782227185489426538793709 7418335194558534952047641)
                ·
                  refine ⟨5563751395918901214035731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7418335194558534952047641 5563751395918901214035731)
                  ·
                    refine ⟨8345627093878351821053597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5563751395918901214035731 8345627093878351821053597)
                    ·
                      refine ⟨3129610160204381932895099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8345627093878351821053597 3129610160204381932895099)
                      ·
                        rfl

theorem cell23_6094894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_6094894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094894 prefixEnd_6094894 := by exact prefixLift 6094894
  have htrace : WordTrace (prefixWord ++ tailWord_6094894) baseStart_6094894 baseEnd_6094894 := by
    simpa [prefixWord, tailWord_6094894, baseEnd_6094894] using wordTrace_append hprefix tailTrace_6094894
  have hstable : (prefixWord ++ tailWord_6094894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094894).length < 2 ^ (prefixWord ++ tailWord_6094894).sum := by decide
  have hdescent : baseEnd_6094894 < baseStart_6094894 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094903 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 5]
def baseStart_6094903 : Nat := 118140960795 + 6094903 * 2 ^ 59
def prefixEnd_6094903 : Nat := 4983230072969 + 3 ^ 40 * 6094903 * 2
def baseEnd_6094903 : Nat := 3129614781530272397682557

theorem tailTrace_6094903 : CollatzResearch.WordTrace tailWord_6094903 prefixEnd_6094903 3129614781530272397682557 := by
  unfold tailWord_6094903
  simp only [CollatzResearch.WordTrace]
  refine ⟨222299375038214832405113363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148199583358809888270075575 222299375038214832405113363)
  ·
    refine ⟨333449062557322248607670045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222299375038214832405113363 333449062557322248607670045)
    ·
      refine ⟨125043398458995843227876267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 333449062557322248607670045 125043398458995843227876267)
      ·
        refine ⟨187565097688493764841814401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125043398458995843227876267 187565097688493764841814401)
        ·
          refine ⟨140673823266370323631360801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187565097688493764841814401 140673823266370323631360801)
          ·
            refine ⟨105505367449777742723520601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140673823266370323631360801 105505367449777742723520601)
            ·
              refine ⟨79129025587333307042640451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105505367449777742723520601 79129025587333307042640451)
              ·
                refine ⟨118693538380999960563960677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79129025587333307042640451 118693538380999960563960677)
                ·
                  refine ⟨22255038446437492605742627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 118693538380999960563960677 22255038446437492605742627)
                  ·
                    refine ⟨33382557669656238908613941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22255038446437492605742627 33382557669656238908613941)
                    ·
                      refine ⟨3129614781530272397682557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33382557669656238908613941 3129614781530272397682557)
                      ·
                        rfl

theorem cell23_6094903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 5].length) (baseStart_6094903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094903 prefixEnd_6094903 := by exact prefixLift 6094903
  have htrace : WordTrace (prefixWord ++ tailWord_6094903) baseStart_6094903 baseEnd_6094903 := by
    simpa [prefixWord, tailWord_6094903, baseEnd_6094903] using wordTrace_append hprefix tailTrace_6094903
  have hstable : (prefixWord ++ tailWord_6094903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094903).length < 2 ^ (prefixWord ++ tailWord_6094903).sum := by decide
  have hdescent : baseEnd_6094903 < baseStart_6094903 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094917 : List Nat := [1, 3, 1, 1, 1, 3, 1, 4, 4, 2, 2]
def baseStart_6094917 : Nat := 118140960795 + 6094917 * 2 ^ 59
def prefixEnd_6094917 : Nat := 4983230072969 + 3 ^ 40 * 6094917 * 2
def baseEnd_6094917 : Nat := 3129621970259435342907493

theorem tailTrace_6094917 : CollatzResearch.WordTrace tailWord_6094917 prefixEnd_6094917 3129621970259435342907493 := by
  unfold tailWord_6094917
  simp only [CollatzResearch.WordTrace]
  refine ⟨222299885660164112796123005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148199923773442741864082003 222299885660164112796123005)
  ·
    refine ⟨83362457122561542298546127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222299885660164112796123005 83362457122561542298546127)
    ·
      refine ⟨125043685683842313447819191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83362457122561542298546127 125043685683842313447819191)
      ·
        refine ⟨187565528525763470171728787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125043685683842313447819191 187565528525763470171728787)
        ·
          refine ⟨281348292788645205257593181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187565528525763470171728787 281348292788645205257593181)
          ·
            refine ⟨105505609795741951971597443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 281348292788645205257593181 105505609795741951971597443)
            ·
              refine ⟨158258414693612927957396165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105505609795741951971597443 158258414693612927957396165)
              ·
                refine ⟨29673452755052423992011781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 158258414693612927957396165 29673452755052423992011781)
                ·
                  refine ⟨5563772391572329498502209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29673452755052423992011781 5563772391572329498502209)
                  ·
                    refine ⟨4172829293679247123876657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5563772391572329498502209 4172829293679247123876657)
                    ·
                      refine ⟨3129621970259435342907493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4172829293679247123876657 3129621970259435342907493)
                      ·
                        rfl

theorem cell23_6094917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 4, 2, 2].length) (baseStart_6094917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094917 prefixEnd_6094917 := by exact prefixLift 6094917
  have htrace : WordTrace (prefixWord ++ tailWord_6094917) baseStart_6094917 baseEnd_6094917 := by
    simpa [prefixWord, tailWord_6094917, baseEnd_6094917] using wordTrace_append hprefix tailTrace_6094917
  have hstable : (prefixWord ++ tailWord_6094917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094917).length < 2 ^ (prefixWord ++ tailWord_6094917).sum := by decide
  have hdescent : baseEnd_6094917 < baseStart_6094917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094940 : List Nat := [2, 2, 4, 1, 1, 2, 1, 3, 7]
def baseStart_6094940 : Nat := 118140960795 + 6094940 * 2 ^ 59
def prefixEnd_6094940 : Nat := 4983230072969 + 3 ^ 40 * 6094940 * 2
def baseEnd_6094940 : Nat := 347737086701609861435543

theorem tailTrace_6094940 : CollatzResearch.WordTrace tailWord_6094940 prefixEnd_6094940 347737086701609861435543 := by
  unfold tailWord_6094940
  simp only [CollatzResearch.WordTrace]
  refine ⟨111150362269540393862105137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148200483026053858482806849 111150362269540393862105137)
  ·
    refine ⟨83362771702155295396578853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111150362269540393862105137 83362771702155295396578853)
    ·
      refine ⟨15630519694154117886858535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83362771702155295396578853 15630519694154117886858535)
      ·
        refine ⟨23445779541231176830287803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15630519694154117886858535 23445779541231176830287803)
        ·
          refine ⟨35168669311846765245431705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23445779541231176830287803 35168669311846765245431705)
          ·
            refine ⟨26376501983885073934073779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35168669311846765245431705 26376501983885073934073779)
            ·
              refine ⟨39564752975827610901110669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26376501983885073934073779 39564752975827610901110669)
              ·
                refine ⟨14836782365935354087916501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39564752975827610901110669 14836782365935354087916501)
                ·
                  refine ⟨347737086701609861435543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14836782365935354087916501 347737086701609861435543)
                  ·
                    rfl

theorem cell23_6094940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 7].length) (baseStart_6094940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094940 prefixEnd_6094940 := by exact prefixLift 6094940
  have htrace : WordTrace (prefixWord ++ tailWord_6094940) baseStart_6094940 baseEnd_6094940 := by
    simpa [prefixWord, tailWord_6094940, baseEnd_6094940] using wordTrace_append hprefix tailTrace_6094940
  have hstable : (prefixWord ++ tailWord_6094940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094940).length < 2 ^ (prefixWord ++ tailWord_6094940).sum := by decide
  have hdescent : baseEnd_6094940 < baseStart_6094940 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094951 : List Nat := [1, 1, 5, 1, 1, 2, 5, 1, 2, 2, 2]
def baseStart_6094951 : Nat := 118140960795 + 6094951 * 2 ^ 59
def prefixEnd_6094951 : Nat := 4983230072969 + 3 ^ 40 * 6094951 * 2
def baseEnd_6094951 : Nat := 3129639428601688209882337

theorem tailTrace_6094951 : CollatzResearch.WordTrace tailWord_6094951 prefixEnd_6094951 3129639428601688209882337 := by
  unfold tailWord_6094951
  simp only [CollatzResearch.WordTrace]
  refine ⟨222301125742040936602860707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148200750494693957735240471 222301125742040936602860707)
  ·
    refine ⟨333451688613061404904291061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222301125742040936602860707 333451688613061404904291061)
    ·
      refine ⟨31261095807474506709777287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 333451688613061404904291061 31261095807474506709777287)
      ·
        refine ⟨46891643711211760064665931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31261095807474506709777287 46891643711211760064665931)
        ·
          refine ⟨70337465566817640096998897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46891643711211760064665931 70337465566817640096998897)
          ·
            refine ⟨52753099175113230072749173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70337465566817640096998897 52753099175113230072749173)
            ·
              refine ⟨4945603047666865319320235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52753099175113230072749173 4945603047666865319320235)
              ·
                refine ⟨7418404571500297978980353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4945603047666865319320235 7418404571500297978980353)
                ·
                  refine ⟨5563803428625223484235265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7418404571500297978980353 5563803428625223484235265)
                  ·
                    refine ⟨4172852571468917613176449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5563803428625223484235265 4172852571468917613176449)
                    ·
                      refine ⟨3129639428601688209882337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4172852571468917613176449 3129639428601688209882337)
                      ·
                        rfl

theorem cell23_6094951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 1, 2, 2, 2].length) (baseStart_6094951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094951 prefixEnd_6094951 := by exact prefixLift 6094951
  have htrace : WordTrace (prefixWord ++ tailWord_6094951) baseStart_6094951 baseEnd_6094951 := by
    simpa [prefixWord, tailWord_6094951, baseEnd_6094951] using wordTrace_append hprefix tailTrace_6094951
  have hstable : (prefixWord ++ tailWord_6094951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094951).length < 2 ^ (prefixWord ++ tailWord_6094951).sum := by decide
  have hdescent : baseEnd_6094951 < baseStart_6094951 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094953 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 3, 7]
def baseStart_6094953 : Nat := 118140960795 + 6094953 * 2 ^ 59
def prefixEnd_6094953 : Nat := 4983230072969 + 3 ^ 40 * 6094953 * 2
def baseEnd_6094953 : Nat := 1043213485187665734019109

theorem tailTrace_6094953 : CollatzResearch.WordTrace tailWord_6094953 prefixEnd_6094953 1043213485187665734019109 := by
  unfold tailWord_6094953
  simp only [CollatzResearch.WordTrace]
  refine ⟨222301198688033690944433513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148200799125355793962955675 222301198688033690944433513)
  ·
    refine ⟨166725899016025268208325135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222301198688033690944433513 166725899016025268208325135)
    ·
      refine ⟨250088848524037902312487703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166725899016025268208325135 250088848524037902312487703)
      ·
        refine ⟨375133272786056853468731555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250088848524037902312487703 375133272786056853468731555)
        ·
          refine ⟨562699909179085280203097333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375133272786056853468731555 562699909179085280203097333)
          ·
            refine ⟨52753116485539245019040375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 562699909179085280203097333 52753116485539245019040375)
            ·
              refine ⟨79129674728308867528560563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52753116485539245019040375 79129674728308867528560563)
              ·
                refine ⟨118694512092463301292840845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79129674728308867528560563 118694512092463301292840845)
                ·
                  refine ⟨44510442034673737984815317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118694512092463301292840845 44510442034673737984815317)
                  ·
                    refine ⟨1043213485187665734019109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44510442034673737984815317 1043213485187665734019109)
                    ·
                      rfl

theorem cell23_6094953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 7].length) (baseStart_6094953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094953 prefixEnd_6094953 := by exact prefixLift 6094953
  have htrace : WordTrace (prefixWord ++ tailWord_6094953) baseStart_6094953 baseEnd_6094953 := by
    simpa [prefixWord, tailWord_6094953, baseEnd_6094953] using wordTrace_append hprefix tailTrace_6094953
  have hstable : (prefixWord ++ tailWord_6094953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094953).length < 2 ^ (prefixWord ++ tailWord_6094953).sum := by decide
  have hdescent : baseEnd_6094953 < baseStart_6094953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6094980 : List Nat := [2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 5]
def baseStart_6094980 : Nat := 118140960795 + 6094980 * 2 ^ 59
def prefixEnd_6094980 : Nat := 4983230072969 + 3 ^ 40 * 6094980 * 2
def baseEnd_6094980 : Nat := 3129654319540668596419703

theorem tailTrace_6094980 : CollatzResearch.WordTrace tailWord_6094980 prefixEnd_6094980 3129654319540668596419703 := by
  unfold tailWord_6094980
  simp only [CollatzResearch.WordTrace]
  refine ⟨111151091729467937277833197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148201455639290583037110929 111151091729467937277833197)
  ·
    refine ⟨41681659398550476479187449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111151091729467937277833197 41681659398550476479187449)
    ·
      refine ⟨31261244548912857359390587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41681659398550476479187449 31261244548912857359390587)
      ·
        refine ⟨46891866823369286039085881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31261244548912857359390587 46891866823369286039085881)
        ·
          refine ⟨35168900117526964529314411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46891866823369286039085881 35168900117526964529314411)
          ·
            refine ⟨52753350176290446793971617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35168900117526964529314411 52753350176290446793971617)
            ·
              refine ⟨39565012632217835095478713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52753350176290446793971617 39565012632217835095478713)
              ·
                refine ⟨29673759474163376321609035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39565012632217835095478713 29673759474163376321609035)
                ·
                  refine ⟨44510639211245064482413553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29673759474163376321609035 44510639211245064482413553)
                  ·
                    refine ⟨33382979408433798361810165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44510639211245064482413553 33382979408433798361810165)
                    ·
                      refine ⟨3129654319540668596419703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33382979408433798361810165 3129654319540668596419703)
                      ·
                        rfl

theorem cell23_6094980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_6094980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6094980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6094980 prefixEnd_6094980 := by exact prefixLift 6094980
  have htrace : WordTrace (prefixWord ++ tailWord_6094980) baseStart_6094980 baseEnd_6094980 := by
    simpa [prefixWord, tailWord_6094980, baseEnd_6094980] using wordTrace_append hprefix tailTrace_6094980
  have hstable : (prefixWord ++ tailWord_6094980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6094980).length < 2 ^ (prefixWord ++ tailWord_6094980).sum := by decide
  have hdescent : baseEnd_6094980 < baseStart_6094980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6094980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095044 : List Nat := [2, 3, 3, 1, 2, 1, 2, 2, 2, 2, 3]
def baseStart_6095044 : Nat := 118140960795 + 6095044 * 2 ^ 59
def prefixEnd_6095044 : Nat := 4983230072969 + 3 ^ 40 * 6095044 * 2
def baseEnd_6095044 : Nat := 3129687182302556346019409

theorem tailTrace_6095044 : CollatzResearch.WordTrace tailWord_6095044 prefixEnd_6095044 3129687182302556346019409 := by
  unfold tailWord_6095044
  simp only [CollatzResearch.WordTrace]
  refine ⟨111152258865352006742998093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148203011820469342323997457 111152258865352006742998093)
  ·
    refine ⟨41682097074507002528624285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111152258865352006742998093 41682097074507002528624285)
    ·
      refine ⟨15630786402940125948234107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41682097074507002528624285 15630786402940125948234107)
      ·
        refine ⟨23446179604410188922351161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15630786402940125948234107 23446179604410188922351161)
        ·
          refine ⟨17584634703307641691763371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23446179604410188922351161 17584634703307641691763371)
          ·
            refine ⟨26376952054961462537645057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17584634703307641691763371 26376952054961462537645057)
            ·
              refine ⟨19782714041221096903233793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26376952054961462537645057 19782714041221096903233793)
              ·
                refine ⟨14837035530915822677425345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19782714041221096903233793 14837035530915822677425345)
                ·
                  refine ⟨11127776648186867008069009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14837035530915822677425345 11127776648186867008069009)
                  ·
                    refine ⟨8345832486140150256051757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11127776648186867008069009 8345832486140150256051757)
                    ·
                      refine ⟨3129687182302556346019409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8345832486140150256051757 3129687182302556346019409)
                      ·
                        rfl

theorem cell23_6095044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_6095044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095044 prefixEnd_6095044 := by exact prefixLift 6095044
  have htrace : WordTrace (prefixWord ++ tailWord_6095044) baseStart_6095044 baseEnd_6095044 := by
    simpa [prefixWord, tailWord_6095044, baseEnd_6095044] using wordTrace_append hprefix tailTrace_6095044
  have hstable : (prefixWord ++ tailWord_6095044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095044).length < 2 ^ (prefixWord ++ tailWord_6095044).sum := by decide
  have hdescent : baseEnd_6095044 < baseStart_6095044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095050 : List Nat := [3, 1, 2, 1, 3, 1, 2, 1, 1, 2, 6]
def baseStart_6095050 : Nat := 118140960795 + 6095050 * 2 ^ 59
def prefixEnd_6095050 : Nat := 4983230072969 + 3 ^ 40 * 6095050 * 2
def baseEnd_6095050 : Nat := 3129690263186483322544381

theorem tailTrace_6095050 : CollatzResearch.WordTrace tailWord_6095050 prefixEnd_6095050 3129690263186483322544381 := by
  unfold tailWord_6095050
  simp only [CollatzResearch.WordTrace]
  refine ⟨55576184142170569127678651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148203157712454851007143069 55576184142170569127678651)
  ·
    refine ⟨83364276213255853691517977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55576184142170569127678651 83364276213255853691517977)
    ·
      refine ⟨62523207159941890268638483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83364276213255853691517977 62523207159941890268638483)
      ·
        refine ⟨93784810739912835402957725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62523207159941890268638483 93784810739912835402957725)
        ·
          refine ⟨35169304027467313276109147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93784810739912835402957725 35169304027467313276109147)
          ·
            refine ⟨52753956041200969914163721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35169304027467313276109147 52753956041200969914163721)
            ·
              refine ⟨39565467030900727435622791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52753956041200969914163721 39565467030900727435622791)
              ·
                refine ⟨59348200546351091153434187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39565467030900727435622791 59348200546351091153434187)
                ·
                  refine ⟨89022300819526636730151281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59348200546351091153434187 89022300819526636730151281)
                  ·
                    refine ⟨66766725614644977547613461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 89022300819526636730151281 66766725614644977547613461)
                    ·
                      refine ⟨3129690263186483322544381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66766725614644977547613461 3129690263186483322544381)
                      ·
                        rfl

theorem cell23_6095050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_6095050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095050 prefixEnd_6095050 := by exact prefixLift 6095050
  have htrace : WordTrace (prefixWord ++ tailWord_6095050) baseStart_6095050 baseEnd_6095050 := by
    simpa [prefixWord, tailWord_6095050, baseEnd_6095050] using wordTrace_append hprefix tailTrace_6095050
  have hstable : (prefixWord ++ tailWord_6095050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095050).length < 2 ^ (prefixWord ++ tailWord_6095050).sum := by decide
  have hdescent : baseEnd_6095050 < baseStart_6095050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095067 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 6, 3, 2]
def baseStart_6095067 : Nat := 118140960795 + 6095067 * 2 ^ 59
def prefixEnd_6095067 : Nat := 4983230072969 + 3 ^ 40 * 6095067 * 2
def baseEnd_6095067 : Nat := 3129698992357609756031803

theorem tailTrace_6095067 : CollatzResearch.WordTrace tailWord_6095067 prefixEnd_6095067 3129698992357609756031803 := by
  unfold tailWord_6095067
  simp only [CollatzResearch.WordTrace]
  refine ⟨222305356609620688414083455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148203571073080458942722303 222305356609620688414083455)
  ·
    refine ⟨333458034914431032621125183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222305356609620688414083455 333458034914431032621125183)
    ·
      refine ⟨500187052371646548931687775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333458034914431032621125183 500187052371646548931687775)
      ·
        refine ⟨750280578557469823397531663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500187052371646548931687775 750280578557469823397531663)
        ·
          refine ⟨1125420867836204735096297495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 750280578557469823397531663 1125420867836204735096297495)
          ·
            refine ⟨1688131301754307102644446243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1125420867836204735096297495 1688131301754307102644446243)
            ·
              refine ⟨2532196952631460653966669365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1688131301754307102644446243 2532196952631460653966669365)
              ·
                refine ⟨237393464309199436309375253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2532196952631460653966669365 237393464309199436309375253)
                ·
                  refine ⟨11127818639493723577001965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 237393464309199436309375253 11127818639493723577001965)
                  ·
                    refine ⟨4172931989810146341375737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11127818639493723577001965 4172931989810146341375737)
                    ·
                      refine ⟨3129698992357609756031803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4172931989810146341375737 3129698992357609756031803)
                      ·
                        rfl

theorem cell23_6095067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6, 3, 2].length) (baseStart_6095067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095067 prefixEnd_6095067 := by exact prefixLift 6095067
  have htrace : WordTrace (prefixWord ++ tailWord_6095067) baseStart_6095067 baseEnd_6095067 := by
    simpa [prefixWord, tailWord_6095067, baseEnd_6095067] using wordTrace_append hprefix tailTrace_6095067
  have hstable : (prefixWord ++ tailWord_6095067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095067).length < 2 ^ (prefixWord ++ tailWord_6095067).sum := by decide
  have hdescent : baseEnd_6095067 < baseStart_6095067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095077 : List Nat := [1, 3, 1, 4, 2, 1, 2, 1, 3, 5]
def baseStart_6095077 : Nat := 118140960795 + 6095077 * 2 ^ 59
def prefixEnd_6095077 : Nat := 4983230072969 + 3 ^ 40 * 6095077 * 2
def baseEnd_6095077 : Nat := 1043234709054718238968919

theorem tailTrace_6095077 : CollatzResearch.WordTrace tailWord_6095077 prefixEnd_6095077 1043234709054718238968919 := by
  unfold tailWord_6095077
  simp only [CollatzResearch.WordTrace]
  refine ⟨222305721339584460121947485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148203814226389640081298323 222305721339584460121947485)
  ·
    refine ⟨83364645502344172545730307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222305721339584460121947485 83364645502344172545730307)
    ·
      refine ⟨125046968253516258818595461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83364645502344172545730307 125046968253516258818595461)
      ·
        refine ⟨23446306547534298528486649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125046968253516258818595461 23446306547534298528486649)
        ·
          refine ⟨17584729910650723896364987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23446306547534298528486649 17584729910650723896364987)
          ·
            refine ⟨26377094865976085844547481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17584729910650723896364987 26377094865976085844547481)
            ·
              refine ⟨19782821149482064383410611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26377094865976085844547481 19782821149482064383410611)
              ·
                refine ⟨29674231724223096575115917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19782821149482064383410611 29674231724223096575115917)
                ·
                  refine ⟨11127836896583661215668469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29674231724223096575115917 11127836896583661215668469)
                  ·
                    refine ⟨1043234709054718238968919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11127836896583661215668469 1043234709054718238968919)
                    ·
                      rfl

theorem cell23_6095077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 3, 5].length) (baseStart_6095077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095077 prefixEnd_6095077 := by exact prefixLift 6095077
  have htrace : WordTrace (prefixWord ++ tailWord_6095077) baseStart_6095077 baseEnd_6095077 := by
    simpa [prefixWord, tailWord_6095077, baseEnd_6095077] using wordTrace_append hprefix tailTrace_6095077
  have hstable : (prefixWord ++ tailWord_6095077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095077).length < 2 ^ (prefixWord ++ tailWord_6095077).sum := by decide
  have hdescent : baseEnd_6095077 < baseStart_6095077 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095091 : List Nat := [1, 1, 1, 2, 2, 4, 4, 3, 1, 1, 3]
def baseStart_6095091 : Nat := 118140960795 + 6095091 * 2 ^ 59
def prefixEnd_6095091 : Nat := 4983230072969 + 3 ^ 40 * 6095091 * 2
def baseEnd_6095091 : Nat := 3129711315893317662131693

theorem tailTrace_6095091 : CollatzResearch.WordTrace tailWord_6095091 prefixEnd_6095091 3129711315893317662131693 := by
  unfold tailWord_6095091
  simp only [CollatzResearch.WordTrace]
  refine ⟨222306231961533740512957127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148204154641022493675304751 222306231961533740512957127)
  ·
    refine ⟨333459347942300610769435691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222306231961533740512957127 333459347942300610769435691)
    ·
      refine ⟨500189021913450916154153537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333459347942300610769435691 500189021913450916154153537)
      ·
        refine ⟨375141766435088187115615153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 500189021913450916154153537 375141766435088187115615153)
        ·
          refine ⟨281356324826316140336711365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 375141766435088187115615153 281356324826316140336711365)
          ·
            refine ⟨52754310904934276313133381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 281356324826316140336711365 52754310904934276313133381)
            ·
              refine ⟨9891433294675176808712509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52754310904934276313133381 9891433294675176808712509)
              ·
                refine ⟨3709287485503191303267191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9891433294675176808712509 3709287485503191303267191)
                ·
                  refine ⟨5563931228254786954900787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3709287485503191303267191 5563931228254786954900787)
                  ·
                    refine ⟨8345896842382180432351181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5563931228254786954900787 8345896842382180432351181)
                    ·
                      refine ⟨3129711315893317662131693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8345896842382180432351181 3129711315893317662131693)
                      ·
                        rfl

theorem cell23_6095091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 3, 1, 1, 3].length) (baseStart_6095091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095091 prefixEnd_6095091 := by exact prefixLift 6095091
  have htrace : WordTrace (prefixWord ++ tailWord_6095091) baseStart_6095091 baseEnd_6095091 := by
    simpa [prefixWord, tailWord_6095091, baseEnd_6095091] using wordTrace_append hprefix tailTrace_6095091
  have hstable : (prefixWord ++ tailWord_6095091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095091).length < 2 ^ (prefixWord ++ tailWord_6095091).sum := by decide
  have hdescent : baseEnd_6095091 < baseStart_6095091 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095107 : List Nat := [1, 1, 1, 3, 2, 3, 3, 1, 4, 4]
def baseStart_6095107 : Nat := 118140960795 + 6095107 * 2 ^ 59
def prefixEnd_6095107 : Nat := 4983230072969 + 3 ^ 40 * 6095107 * 2
def baseEnd_6095107 : Nat := 1043239843861263199843873

theorem tailTrace_6095107 : CollatzResearch.WordTrace tailWord_6095107 prefixEnd_6095107 1043239843861263199843873 := by
  unfold tailWord_6095107
  simp only [CollatzResearch.WordTrace]
  refine ⟨222306815529475775245539575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148204543686317183497026383 222306815529475775245539575)
  ·
    refine ⟨333460223294213662868309363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222306815529475775245539575 333460223294213662868309363)
    ·
      refine ⟨500190334941320494302464045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333460223294213662868309363 500190334941320494302464045)
      ·
        refine ⟨187571375602995185363424017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 500190334941320494302464045 187571375602995185363424017)
        ·
          refine ⟨140678531702246389022568013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187571375602995185363424017 140678531702246389022568013)
          ·
            refine ⟨52754449388342395883463005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140678531702246389022568013 52754449388342395883463005)
            ·
              refine ⟨19782918520628398456298627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52754449388342395883463005 19782918520628398456298627)
              ·
                refine ⟨29674377780942597684447941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19782918520628398456298627 29674377780942597684447941)
                ·
                  refine ⟨5563945833926737065833989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29674377780942597684447941 5563945833926737065833989)
                  ·
                    refine ⟨1043239843861263199843873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5563945833926737065833989 1043239843861263199843873)
                    ·
                      rfl

theorem cell23_6095107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 4, 4].length) (baseStart_6095107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095107 prefixEnd_6095107 := by exact prefixLift 6095107
  have htrace : WordTrace (prefixWord ++ tailWord_6095107) baseStart_6095107 baseEnd_6095107 := by
    simpa [prefixWord, tailWord_6095107, baseEnd_6095107] using wordTrace_append hprefix tailTrace_6095107
  have hstable : (prefixWord ++ tailWord_6095107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095107).length < 2 ^ (prefixWord ++ tailWord_6095107).sum := by decide
  have hdescent : baseEnd_6095107 < baseStart_6095107 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095127 : List Nat := [1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 6]
def baseStart_6095127 : Nat := 118140960795 + 6095127 * 2 ^ 59
def prefixEnd_6095127 : Nat := 4983230072969 + 3 ^ 40 * 6095127 * 2
def baseEnd_6095127 : Nat := 3129729801196879521281527

theorem tailTrace_6095127 : CollatzResearch.WordTrace tailWord_6095127 prefixEnd_6095127 3129729801196879521281527 := by
  unfold tailWord_6095127
  simp only [CollatzResearch.WordTrace]
  refine ⟨222307544989403318661267635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148205029992935545774178423 222307544989403318661267635)
  ·
    refine ⟨333461317484104977991901453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222307544989403318661267635 333461317484104977991901453)
    ·
      refine ⟨125047994056539366746963045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 333461317484104977991901453 125047994056539366746963045)
      ·
        refine ⟨23446498885601131265055571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125047994056539366746963045 23446498885601131265055571)
        ·
          refine ⟨35169748328401696897583357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23446498885601131265055571 35169748328401696897583357)
          ·
            refine ⟨13188655623150636336593759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35169748328401696897583357 13188655623150636336593759)
            ·
              refine ⟨19782983434725954504890639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13188655623150636336593759 19782983434725954504890639)
              ·
                refine ⟨29674475152088931757335959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19782983434725954504890639 29674475152088931757335959)
                ·
                  refine ⟨44511712728133397636003939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29674475152088931757335959 44511712728133397636003939)
                  ·
                    refine ⟨66767569092200096454005909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44511712728133397636003939 66767569092200096454005909)
                    ·
                      refine ⟨3129729801196879521281527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66767569092200096454005909 3129729801196879521281527)
                      ·
                        rfl

theorem cell23_6095127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_6095127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095127 prefixEnd_6095127 := by exact prefixLift 6095127
  have htrace : WordTrace (prefixWord ++ tailWord_6095127) baseStart_6095127 baseEnd_6095127 := by
    simpa [prefixWord, tailWord_6095127, baseEnd_6095127] using wordTrace_append hprefix tailTrace_6095127
  have hstable : (prefixWord ++ tailWord_6095127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095127).length < 2 ^ (prefixWord ++ tailWord_6095127).sum := by decide
  have hdescent : baseEnd_6095127 < baseStart_6095127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095137 : List Nat := [1, 2, 3, 2, 1, 1, 6, 7]
def baseStart_6095137 : Nat := 118140960795 + 6095137 * 2 ^ 59
def prefixEnd_6095137 : Nat := 4983230072969 + 3 ^ 40 * 6095137 * 2
def baseEnd_6095137 : Nat := 115916108740867573413203

theorem tailTrace_6095137 : CollatzResearch.WordTrace tailWord_6095137 prefixEnd_6095137 115916108740867573413203 := by
  unfold tailWord_6095137
  simp only [CollatzResearch.WordTrace]
  refine ⟨222307909719367090369131665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148205273146244726912754443 222307909719367090369131665)
  ·
    refine ⟨166730932289525317776848749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222307909719367090369131665 166730932289525317776848749)
    ·
      refine ⟨62524099608571994166318281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166730932289525317776848749 62524099608571994166318281)
      ·
        refine ⟨46893074706428995624738711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62524099608571994166318281 46893074706428995624738711)
        ·
          refine ⟨70339612059643493437108067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46893074706428995624738711 70339612059643493437108067)
          ·
            refine ⟨105509418089465240155662101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70339612059643493437108067 105509418089465240155662101)
            ·
              refine ⟨4945753972943683132296661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 105509418089465240155662101 4945753972943683132296661)
              ·
                refine ⟨115916108740867573413203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4945753972943683132296661 115916108740867573413203)
                ·
                  rfl

theorem cell23_6095137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 7].length) (baseStart_6095137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095137 prefixEnd_6095137 := by exact prefixLift 6095137
  have htrace : WordTrace (prefixWord ++ tailWord_6095137) baseStart_6095137 baseEnd_6095137 := by
    simpa [prefixWord, tailWord_6095137, baseEnd_6095137] using wordTrace_append hprefix tailTrace_6095137
  have hstable : (prefixWord ++ tailWord_6095137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095137).length < 2 ^ (prefixWord ++ tailWord_6095137).sum := by decide
  have hdescent : baseEnd_6095137 < baseStart_6095137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095148 : List Nat := [2, 2, 1, 1, 1, 3, 5, 3, 1, 2, 2]
def baseStart_6095148 : Nat := 118140960795 + 6095148 * 2 ^ 59
def prefixEnd_6095148 : Nat := 4983230072969 + 3 ^ 40 * 6095148 * 2
def baseEnd_6095148 : Nat := 3129740584290623939118931

theorem tailTrace_6095148 : CollatzResearch.WordTrace tailWord_6095148 prefixEnd_6095148 3129740584290623939118931 := by
  unfold tailWord_6095148
  simp only [CollatzResearch.WordTrace]
  refine ⟨111154155461163619623891049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148205540614884826165188065 111154155461163619623891049)
  ·
    refine ⟨83365616595872714717918287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111154155461163619623891049 83365616595872714717918287)
    ·
      refine ⟨125048424893809072076877431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83365616595872714717918287 125048424893809072076877431)
      ·
        refine ⟨187572637340713608115316147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125048424893809072076877431 187572637340713608115316147)
        ·
          refine ⟨281358956011070412172974221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187572637340713608115316147 281358956011070412172974221)
          ·
            refine ⟨105509608504151404564865333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 281358956011070412172974221 105509608504151404564865333)
            ·
              refine ⟨9891525797264194177956125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 105509608504151404564865333 9891525797264194177956125)
              ·
                refine ⟨3709322173974072816733547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9891525797264194177956125 3709322173974072816733547)
                ·
                  refine ⟨5563983260961109225100321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3709322173974072816733547 5563983260961109225100321)
                  ·
                    refine ⟨4172987445720831918825241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5563983260961109225100321 4172987445720831918825241)
                    ·
                      refine ⟨3129740584290623939118931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4172987445720831918825241 3129740584290623939118931)
                      ·
                        rfl

theorem cell23_6095148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 3, 1, 2, 2].length) (baseStart_6095148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095148 prefixEnd_6095148 := by exact prefixLift 6095148
  have htrace : WordTrace (prefixWord ++ tailWord_6095148) baseStart_6095148 baseEnd_6095148 := by
    simpa [prefixWord, tailWord_6095148, baseEnd_6095148] using wordTrace_append hprefix tailTrace_6095148
  have hstable : (prefixWord ++ tailWord_6095148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095148).length < 2 ^ (prefixWord ++ tailWord_6095148).sum := by decide
  have hdescent : baseEnd_6095148 < baseStart_6095148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095154 : List Nat := [3, 2, 1, 1, 6, 1, 9]
def baseStart_6095154 : Nat := 118140960795 + 6095154 * 2 ^ 59
def prefixEnd_6095154 : Nat := 4983230072969 + 3 ^ 40 * 6095154 * 2
def baseEnd_6095154 : Nat := 38638810681167295254863

theorem tailTrace_6095154 : CollatzResearch.WordTrace tailWord_6095154 prefixEnd_6095154 38638810681167295254863 := by
  unfold tailWord_6095154
  simp only [CollatzResearch.WordTrace]
  refine ⟨55577132440076375568125129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148205686506870334848333677 55577132440076375568125129)
  ·
    refine ⟨41682849330057281676093847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55577132440076375568125129 41682849330057281676093847)
    ·
      refine ⟨62524273995085922514140771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41682849330057281676093847 62524273995085922514140771)
      ·
        refine ⟨93786410992628883771211157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62524273995085922514140771 93786410992628883771211157)
        ·
          refine ⟨4396238015279478926775523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 93786410992628883771211157 4396238015279478926775523)
          ·
            refine ⟨6594357022919218390163285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4396238015279478926775523 6594357022919218390163285)
            ·
              refine ⟨38638810681167295254863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6594357022919218390163285 38638810681167295254863)
              ·
                rfl

theorem cell23_6095154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 9].length) (baseStart_6095154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095154 prefixEnd_6095154 := by exact prefixLift 6095154
  have htrace : WordTrace (prefixWord ++ tailWord_6095154) baseStart_6095154 baseEnd_6095154 := by
    simpa [prefixWord, tailWord_6095154, baseEnd_6095154] using wordTrace_append hprefix tailTrace_6095154
  have hstable : (prefixWord ++ tailWord_6095154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095154).length < 2 ^ (prefixWord ++ tailWord_6095154).sum := by decide
  have hdescent : baseEnd_6095154 < baseStart_6095154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095164 : List Nat := [2, 2, 2, 2, 1, 2, 1, 3, 4, 1, 3]
def baseStart_6095164 : Nat := 118140960795 + 6095164 * 2 ^ 59
def prefixEnd_6095164 : Nat := 4983230072969 + 3 ^ 40 * 6095164 * 2
def baseEnd_6095164 : Nat := 3129748799981095876518857

theorem tailTrace_6095164 : CollatzResearch.WordTrace tailWord_6095164 prefixEnd_6095164 3129748799981095876518857 := by
  unfold tailWord_6095164
  simp only [CollatzResearch.WordTrace]
  refine ⟨111154447245134636990182273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148205929660179515986909697 111154447245134636990182273)
  ·
    refine ⟨83365835433850977742636705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111154447245134636990182273 83365835433850977742636705)
    ·
      refine ⟨62524376575388233306977529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83365835433850977742636705 62524376575388233306977529)
      ·
        refine ⟨46893282431541174980233147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62524376575388233306977529 46893282431541174980233147)
        ·
          refine ⟨70339923647311762470349721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46893282431541174980233147 70339923647311762470349721)
          ·
            refine ⟨52754942735483821852762291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70339923647311762470349721 52754942735483821852762291)
            ·
              refine ⟨79132414103225732779143437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52754942735483821852762291 79132414103225732779143437)
              ·
                refine ⟨29674655288709649792178789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79132414103225732779143437 29674655288709649792178789)
                ·
                  refine ⟨5563997866633059336033523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29674655288709649792178789 5563997866633059336033523)
                  ·
                    refine ⟨8345996799949589004050285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5563997866633059336033523 8345996799949589004050285)
                    ·
                      refine ⟨3129748799981095876518857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8345996799949589004050285 3129748799981095876518857)
                      ·
                        rfl

theorem cell23_6095164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_6095164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095164 prefixEnd_6095164 := by exact prefixLift 6095164
  have htrace : WordTrace (prefixWord ++ tailWord_6095164) baseStart_6095164 baseEnd_6095164 := by
    simpa [prefixWord, tailWord_6095164, baseEnd_6095164] using wordTrace_append hprefix tailTrace_6095164
  have hstable : (prefixWord ++ tailWord_6095164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095164).length < 2 ^ (prefixWord ++ tailWord_6095164).sum := by decide
  have hdescent : baseEnd_6095164 < baseStart_6095164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095217 : List Nat := [1, 2, 2, 2, 1, 2, 1, 4, 2, 2, 4]
def baseStart_6095217 : Nat := 118140960795 + 6095217 * 2 ^ 59
def prefixEnd_6095217 : Nat := 4983230072969 + 3 ^ 40 * 6095217 * 2
def baseEnd_6095217 : Nat := 3129776014455784169156113

theorem tailTrace_6095217 : CollatzResearch.WordTrace tailWord_6095217 prefixEnd_6095217 3129776014455784169156113 := by
  unfold tailWord_6095217
  simp only [CollatzResearch.WordTrace]
  refine ⟨222310827559077264032043905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148207218372718176021362603 222310827559077264032043905)
  ·
    refine ⟨166733120669307948024032929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222310827559077264032043905 166733120669307948024032929)
    ·
      refine ⟨125049840501980961018024697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166733120669307948024032929 125049840501980961018024697)
      ·
        refine ⟨93787380376485720763518523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125049840501980961018024697 93787380376485720763518523)
        ·
          refine ⟨140681070564728581145277785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93787380376485720763518523 140681070564728581145277785)
          ·
            refine ⟨105510802923546435858958339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140681070564728581145277785 105510802923546435858958339)
            ·
              refine ⟨158266204385319653788437509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105510802923546435858958339 158266204385319653788437509)
              ·
                refine ⟨29674913322247435085332033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 158266204385319653788437509 29674913322247435085332033)
                ·
                  refine ⟨22256184991685576313999025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29674913322247435085332033 22256184991685576313999025)
                  ·
                    refine ⟨16692138743764182235499269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22256184991685576313999025 16692138743764182235499269)
                    ·
                      refine ⟨3129776014455784169156113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16692138743764182235499269 3129776014455784169156113)
                      ·
                        rfl

theorem cell23_6095217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_6095217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095217 prefixEnd_6095217 := by exact prefixLift 6095217
  have htrace : WordTrace (prefixWord ++ tailWord_6095217) baseStart_6095217 baseEnd_6095217 := by
    simpa [prefixWord, tailWord_6095217, baseEnd_6095217] using wordTrace_append hprefix tailTrace_6095217
  have hstable : (prefixWord ++ tailWord_6095217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095217).length < 2 ^ (prefixWord ++ tailWord_6095217).sum := by decide
  have hdescent : baseEnd_6095217 < baseStart_6095217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095257 : List Nat := [1, 2, 1, 2, 1, 4, 3, 1, 1, 7]
def baseStart_6095257 : Nat := 118140960795 + 6095257 * 2 ^ 59
def prefixEnd_6095257 : Nat := 4983230072969 + 3 ^ 40 * 6095257 * 2
def baseEnd_6095257 : Nat := 1043265517893988004218643

theorem tailTrace_6095257 : CollatzResearch.WordTrace tailWord_6095257 prefixEnd_6095257 1043265517893988004218643 := by
  unfold tailWord_6095257
  simp only [CollatzResearch.WordTrace]
  refine ⟨222312286478932350863500025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148208190985954900575666683 222312286478932350863500025)
  ·
    refine ⟨166734214859199263147625019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222312286478932350863500025 166734214859199263147625019)
    ·
      refine ⟨250101322288798894721437529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166734214859199263147625019 250101322288798894721437529)
      ·
        refine ⟨187575991716599171041078147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250101322288798894721437529 187575991716599171041078147)
        ·
          refine ⟨281363987574898756561617221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187575991716599171041078147 281363987574898756561617221)
          ·
            refine ⟨52755747670293516855303229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 281363987574898756561617221 52755747670293516855303229)
            ·
              refine ⟨19783405376360068820738711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52755747670293516855303229 19783405376360068820738711)
              ·
                refine ⟨29675108064540103231108067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19783405376360068820738711 29675108064540103231108067)
                ·
                  refine ⟨44512662096810154846662101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29675108064540103231108067 44512662096810154846662101)
                  ·
                    refine ⟨1043265517893988004218643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44512662096810154846662101 1043265517893988004218643)
                    ·
                      rfl

theorem cell23_6095257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 7].length) (baseStart_6095257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095257 prefixEnd_6095257 := by exact prefixLift 6095257
  have htrace : WordTrace (prefixWord ++ tailWord_6095257) baseStart_6095257 baseEnd_6095257 := by
    simpa [prefixWord, tailWord_6095257, baseEnd_6095257] using wordTrace_append hprefix tailTrace_6095257
  have hstable : (prefixWord ++ tailWord_6095257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095257).length < 2 ^ (prefixWord ++ tailWord_6095257).sum := by decide
  have hdescent : baseEnd_6095257 < baseStart_6095257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095272 : List Nat := [2, 1, 6, 1, 1, 3, 1, 2, 2, 2, 2]
def baseStart_6095272 : Nat := 118140960795 + 6095272 * 2 ^ 59
def prefixEnd_6095272 : Nat := 4983230072969 + 3 ^ 40 * 6095272 * 2
def baseEnd_6095272 : Nat := 3129804255891781453968361

theorem tailTrace_6095272 : CollatzResearch.WordTrace tailWord_6095272 prefixEnd_6095272 3129804255891781453968361 := by
  unfold tailWord_6095272
  simp only [CollatzResearch.WordTrace]
  refine ⟨111156416786939004212648035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148208555715918672283530713 111156416786939004212648035)
  ·
    refine ⟨166734625180408506318972053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111156416786939004212648035 166734625180408506318972053)
    ·
      refine ⟨7815685555331648733701815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 166734625180408506318972053 7815685555331648733701815)
      ·
        refine ⟨11723528332997473100552723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7815685555331648733701815 11723528332997473100552723)
        ·
          refine ⟨17585292499496209650829085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11723528332997473100552723 17585292499496209650829085)
          ·
            refine ⟨6594484687311078619060907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17585292499496209650829085 6594484687311078619060907)
            ·
              refine ⟨9891727030966617928591361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6594484687311078619060907 9891727030966617928591361)
              ·
                refine ⟨7418795273224963446443521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9891727030966617928591361 7418795273224963446443521)
                ·
                  refine ⟨5564096454918722584832641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7418795273224963446443521 5564096454918722584832641)
                  ·
                    refine ⟨4173072341189041938624481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5564096454918722584832641 4173072341189041938624481)
                    ·
                      refine ⟨3129804255891781453968361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4173072341189041938624481 3129804255891781453968361)
                      ·
                        rfl

theorem cell23_6095272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_6095272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095272 prefixEnd_6095272 := by exact prefixLift 6095272
  have htrace : WordTrace (prefixWord ++ tailWord_6095272) baseStart_6095272 baseEnd_6095272 := by
    simpa [prefixWord, tailWord_6095272, baseEnd_6095272] using wordTrace_append hprefix tailTrace_6095272
  have hstable : (prefixWord ++ tailWord_6095272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095272).length < 2 ^ (prefixWord ++ tailWord_6095272).sum := by decide
  have hdescent : baseEnd_6095272 < baseStart_6095272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095294 : List Nat := [4, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4]
def baseStart_6095294 : Nat := 118140960795 + 6095294 * 2 ^ 59
def prefixEnd_6095294 : Nat := 4983230072969 + 3 ^ 40 * 6095294 * 2
def baseEnd_6095294 : Nat := 3129815552466180367893259

theorem tailTrace_6095294 : CollatzResearch.WordTrace tailWord_6095294 prefixEnd_6095294 3129815552466180367893259 := by
  unfold tailWord_6095294
  simp only [CollatzResearch.WordTrace]
  refine ⟨27789204497474788272824617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148209090653198870788397957 27789204497474788272824617)
  ·
    refine ⟨20841903373106091204618463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27789204497474788272824617 20841903373106091204618463)
    ·
      refine ⟨31262855059659136806927695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20841903373106091204618463 31262855059659136806927695)
      ·
        refine ⟨46894282589488705210391543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31262855059659136806927695 46894282589488705210391543)
        ·
          refine ⟨70341423884233057815587315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46894282589488705210391543 70341423884233057815587315)
          ·
            refine ⟨105512135826349586723380973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70341423884233057815587315 105512135826349586723380973)
            ·
              refine ⟨39567050934881095021267865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105512135826349586723380973 39567050934881095021267865)
              ·
                refine ⟨29675288201160821265950899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39567050934881095021267865 29675288201160821265950899)
                ·
                  refine ⟨44512932301741231898926349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29675288201160821265950899 44512932301741231898926349)
                  ·
                    refine ⟨16692349613152961962097381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44512932301741231898926349 16692349613152961962097381)
                    ·
                      refine ⟨3129815552466180367893259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16692349613152961962097381 3129815552466180367893259)
                      ·
                        rfl

theorem cell23_6095294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_6095294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095294 prefixEnd_6095294 := by exact prefixLift 6095294
  have htrace : WordTrace (prefixWord ++ tailWord_6095294) baseStart_6095294 baseEnd_6095294 := by
    simpa [prefixWord, tailWord_6095294, baseEnd_6095294] using wordTrace_append hprefix tailTrace_6095294
  have hstable : (prefixWord ++ tailWord_6095294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095294).length < 2 ^ (prefixWord ++ tailWord_6095294).sum := by decide
  have hdescent : baseEnd_6095294 < baseStart_6095294 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095307 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 1, 6, 4]
def baseStart_6095307 : Nat := 118140960795 + 6095307 * 2 ^ 59
def prefixEnd_6095307 : Nat := 4983230072969 + 3 ^ 40 * 6095307 * 2
def baseEnd_6095307 : Nat := 3129822227714688817030699

theorem tailTrace_6095307 : CollatzResearch.WordTrace tailWord_6095307 prefixEnd_6095307 3129822227714688817030699 := by
  unfold tailWord_6095307
  simp only [CollatzResearch.WordTrace]
  refine ⟨222314110128751209402820175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148209406752500806268546783 222314110128751209402820175)
  ·
    refine ⟨333471165193126814104230263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222314110128751209402820175 333471165193126814104230263)
    ·
      refine ⟨500206747789690221156345395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333471165193126814104230263 500206747789690221156345395)
      ·
        refine ⟨750310121684535331734518093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500206747789690221156345395 750310121684535331734518093)
        ·
          refine ⟨281366295631700749400444285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 750310121684535331734518093 281366295631700749400444285)
          ·
            refine ⟨105512360861887781025166607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 281366295631700749400444285 105512360861887781025166607)
            ·
              refine ⟨158268541292831671537749911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105512360861887781025166607 158268541292831671537749911)
              ·
                refine ⟨237402811939247507306624867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158268541292831671537749911 237402811939247507306624867)
                ·
                  refine ⟨356104217908871260959937301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 237402811939247507306624867 356104217908871260959937301)
                  ·
                    refine ⟨16692385214478340357497061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 356104217908871260959937301 16692385214478340357497061)
                    ·
                      refine ⟨3129822227714688817030699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16692385214478340357497061 3129822227714688817030699)
                      ·
                        rfl

theorem cell23_6095307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 6, 4].length) (baseStart_6095307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095307 prefixEnd_6095307 := by exact prefixLift 6095307
  have htrace : WordTrace (prefixWord ++ tailWord_6095307) baseStart_6095307 baseEnd_6095307 := by
    simpa [prefixWord, tailWord_6095307, baseEnd_6095307] using wordTrace_append hprefix tailTrace_6095307
  have hstable : (prefixWord ++ tailWord_6095307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095307).length < 2 ^ (prefixWord ++ tailWord_6095307).sum := by decide
  have hdescent : baseEnd_6095307 < baseStart_6095307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095337 : List Nat := [1, 2, 1, 1, 1, 2, 1, 5, 1, 2, 6]
def baseStart_6095337 : Nat := 118140960795 + 6095337 * 2 ^ 59
def prefixEnd_6095337 : Nat := 4983230072969 + 3 ^ 40 * 6095337 * 2
def baseEnd_6095337 : Nat := 3129837632134323699655561

theorem tailTrace_6095337 : CollatzResearch.WordTrace tailWord_6095337 prefixEnd_6095337 3129837632134323699655561 := by
  unfold tailWord_6095337
  simp only [CollatzResearch.WordTrace]
  refine ⟨222315204318642524526412265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148210136212428349684274843 222315204318642524526412265)
  ·
    refine ⟨166736403238981893394809199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222315204318642524526412265 166736403238981893394809199)
    ·
      refine ⟨250104604858472840092213799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166736403238981893394809199 250104604858472840092213799)
      ·
        refine ⟨375156907287709260138320699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250104604858472840092213799 375156907287709260138320699)
        ·
          refine ⟨562735360931563890207481049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375156907287709260138320699 562735360931563890207481049)
          ·
            refine ⟨422051520698672917655610787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 562735360931563890207481049 422051520698672917655610787)
            ·
              refine ⟨633077281048009376483416181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 422051520698672917655610787 633077281048009376483416181)
              ·
                refine ⟨59350995098250879045320267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 633077281048009376483416181 59350995098250879045320267)
                ·
                  refine ⟨89026492647376318567980401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59350995098250879045320267 89026492647376318567980401)
                  ·
                    refine ⟨66769869485532238925985301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 89026492647376318567980401 66769869485532238925985301)
                    ·
                      refine ⟨3129837632134323699655561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66769869485532238925985301 3129837632134323699655561)
                      ·
                        rfl

theorem cell23_6095337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 2, 6].length) (baseStart_6095337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095337 prefixEnd_6095337 := by exact prefixLift 6095337
  have htrace : WordTrace (prefixWord ++ tailWord_6095337) baseStart_6095337 baseEnd_6095337 := by
    simpa [prefixWord, tailWord_6095337, baseEnd_6095337] using wordTrace_append hprefix tailTrace_6095337
  have hstable : (prefixWord ++ tailWord_6095337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095337).length < 2 ^ (prefixWord ++ tailWord_6095337).sum := by decide
  have hdescent : baseEnd_6095337 < baseStart_6095337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095338 : List Nat := [3, 1, 3, 1, 3, 3, 1, 1, 3, 4]
def baseStart_6095338 : Nat := 118140960795 + 6095338 * 2 ^ 59
def prefixEnd_6095338 : Nat := 4983230072969 + 3 ^ 40 * 6095338 * 2
def baseEnd_6095338 : Nat := 1043279381871659398581019

theorem tailTrace_6095338 : CollatzResearch.WordTrace tailWord_6095338 prefixEnd_6095338 1043279381871659398581019 := by
  unfold tailWord_6095338
  simp only [CollatzResearch.WordTrace]
  refine ⟨55578810197909725424299667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148210160527759267798132445 55578810197909725424299667)
  ·
    refine ⟨83368215296864588136449501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55578810197909725424299667 83368215296864588136449501)
    ·
      refine ⟨31263080736324220551168563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83368215296864588136449501 31263080736324220551168563)
      ·
        refine ⟨46894621104486330826752845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31263080736324220551168563 46894621104486330826752845)
        ·
          refine ⟨17585482914182374060032317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46894621104486330826752845 17585482914182374060032317)
          ·
            refine ⟨6594556092818390272512119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17585482914182374060032317 6594556092818390272512119)
            ·
              refine ⟨9891834139227585408768179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6594556092818390272512119 9891834139227585408768179)
              ·
                refine ⟨14837751208841378113152269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9891834139227585408768179 14837751208841378113152269)
                ·
                  refine ⟨5564156703315516792432101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14837751208841378113152269 5564156703315516792432101)
                  ·
                    refine ⟨1043279381871659398581019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5564156703315516792432101 1043279381871659398581019)
                    ·
                      rfl

theorem cell23_6095338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_6095338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095338 prefixEnd_6095338 := by exact prefixLift 6095338
  have htrace : WordTrace (prefixWord ++ tailWord_6095338) baseStart_6095338 baseEnd_6095338 := by
    simpa [prefixWord, tailWord_6095338, baseEnd_6095338] using wordTrace_append hprefix tailTrace_6095338
  have hstable : (prefixWord ++ tailWord_6095338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095338).length < 2 ^ (prefixWord ++ tailWord_6095338).sum := by decide
  have hdescent : baseEnd_6095338 < baseStart_6095338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095388 : List Nat := [2, 2, 3, 1, 2, 2, 2, 2, 2, 3, 2]
def baseStart_6095388 : Nat := 118140960795 + 6095388 * 2 ^ 59
def prefixEnd_6095388 : Nat := 4983230072969 + 3 ^ 40 * 6095388 * 2
def baseEnd_6095388 : Nat := 3129863819647703000117827

theorem tailTrace_6095388 : CollatzResearch.WordTrace tailWord_6095388 prefixEnd_6095388 3129863819647703000117827 := by
  unfold tailWord_6095388
  simp only [CollatzResearch.WordTrace]
  refine ⟨111158532220728880118259409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148211376294305173491012545 111158532220728880118259409)
  ·
    refine ⟨83368899165546660088694557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111158532220728880118259409 83368899165546660088694557)
    ·
      refine ⟨31263337187079997533260459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83368899165546660088694557 31263337187079997533260459)
      ·
        refine ⟨46895005780619996299890689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31263337187079997533260459 46895005780619996299890689)
        ·
          refine ⟨35171254335464997224918017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46895005780619996299890689 35171254335464997224918017)
          ·
            refine ⟨26378440751598747918688513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35171254335464997224918017 26378440751598747918688513)
            ·
              refine ⟨19783830563699060939016385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26378440751598747918688513 19783830563699060939016385)
              ·
                refine ⟨14837872922774295704262289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19783830563699060939016385 14837872922774295704262289)
                ·
                  refine ⟨11128404692080721778196717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14837872922774295704262289 11128404692080721778196717)
                  ·
                    refine ⟨4173151759530270666823769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11128404692080721778196717 4173151759530270666823769)
                    ·
                      refine ⟨3129863819647703000117827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4173151759530270666823769 3129863819647703000117827)
                      ·
                        rfl

theorem cell23_6095388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 2, 3, 2].length) (baseStart_6095388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095388 prefixEnd_6095388 := by exact prefixLift 6095388
  have htrace : WordTrace (prefixWord ++ tailWord_6095388) baseStart_6095388 baseEnd_6095388 := by
    simpa [prefixWord, tailWord_6095388, baseEnd_6095388] using wordTrace_append hprefix tailTrace_6095388
  have hstable : (prefixWord ++ tailWord_6095388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095388).length < 2 ^ (prefixWord ++ tailWord_6095388).sum := by decide
  have hdescent : baseEnd_6095388 < baseStart_6095388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095394 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 5, 6]
def baseStart_6095394 : Nat := 118140960795 + 6095394 * 2 ^ 59
def prefixEnd_6095394 : Nat := 4983230072969 + 3 ^ 40 * 6095394 * 2
def baseEnd_6095394 : Nat := 1043288966843876658880933

theorem tailTrace_6095394 : CollatzResearch.WordTrace tailWord_6095394 prefixEnd_6095394 1043288966843876658880933 := by
  unfold tailWord_6095394
  simp only [CollatzResearch.WordTrace]
  refine ⟨55579320819859005815309309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148211522186290682174158157 55579320819859005815309309)
  ·
    refine ⟨20842245307447127180740991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55579320819859005815309309 20842245307447127180740991)
    ·
      refine ⟨31263367961170690771111487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20842245307447127180740991 31263367961170690771111487)
      ·
        refine ⟨46895051941756036156667231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31263367961170690771111487 46895051941756036156667231)
        ·
          refine ⟨70342577912634054235000847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46895051941756036156667231 70342577912634054235000847)
          ·
            refine ⟨105513866868951081352501271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70342577912634054235000847 105513866868951081352501271)
            ·
              refine ⟨158270800303426622028751907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105513866868951081352501271 158270800303426622028751907)
              ·
                refine ⟨237406200455139933043127861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158270800303426622028751907 237406200455139933043127861)
                ·
                  refine ⟨22256831292669368722793237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 237406200455139933043127861 22256831292669368722793237)
                  ·
                    refine ⟨1043288966843876658880933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22256831292669368722793237 1043288966843876658880933)
                    ·
                      rfl

theorem cell23_6095394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_6095394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095394 prefixEnd_6095394 := by exact prefixLift 6095394
  have htrace : WordTrace (prefixWord ++ tailWord_6095394) baseStart_6095394 baseEnd_6095394 := by
    simpa [prefixWord, tailWord_6095394, baseEnd_6095394] using wordTrace_append hprefix tailTrace_6095394
  have hstable : (prefixWord ++ tailWord_6095394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095394).length < 2 ^ (prefixWord ++ tailWord_6095394).sum := by decide
  have hdescent : baseEnd_6095394 < baseStart_6095394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095395 : List Nat := [1, 1, 1, 4, 4, 2, 1, 4, 1, 1, 3]
def baseStart_6095395 : Nat := 118140960795 + 6095395 * 2 ^ 59
def prefixEnd_6095395 : Nat := 4983230072969 + 3 ^ 40 * 6095395 * 2
def baseEnd_6095395 : Nat := 3129867414012284472730295

theorem tailTrace_6095395 : CollatzResearch.WordTrace tailWord_6095395 prefixEnd_6095395 3129867414012284472730295 := by
  unfold tailWord_6095395
  simp only [CollatzResearch.WordTrace]
  refine ⟨222317319752432400432023639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148211546501621600288015759 222317319752432400432023639)
  ·
    refine ⟨333475979628648600648035459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222317319752432400432023639 333475979628648600648035459)
    ·
      refine ⟨500213969442972900972053189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333475979628648600648035459 500213969442972900972053189)
      ·
        refine ⟨93790119270557418932259973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 500213969442972900972053189 93790119270557418932259973)
        ·
          refine ⟨17585647363229516049798745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93790119270557418932259973 17585647363229516049798745)
          ·
            refine ⟨13189235522422137037349059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17585647363229516049798745 13189235522422137037349059)
            ·
              refine ⟨19783853283633205556023589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13189235522422137037349059 19783853283633205556023589)
              ·
                refine ⟨3709472490681226041754423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19783853283633205556023589 3709472490681226041754423)
                ·
                  refine ⟨5564208736021839062631635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3709472490681226041754423 5564208736021839062631635)
                  ·
                    refine ⟨8346313104032758593947453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5564208736021839062631635 8346313104032758593947453)
                    ·
                      refine ⟨3129867414012284472730295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8346313104032758593947453 3129867414012284472730295)
                      ·
                        rfl

theorem cell23_6095395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 4, 1, 1, 3].length) (baseStart_6095395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095395 prefixEnd_6095395 := by exact prefixLift 6095395
  have htrace : WordTrace (prefixWord ++ tailWord_6095395) baseStart_6095395 baseEnd_6095395 := by
    simpa [prefixWord, tailWord_6095395, baseEnd_6095395] using wordTrace_append hprefix tailTrace_6095395
  have hstable : (prefixWord ++ tailWord_6095395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095395).length < 2 ^ (prefixWord ++ tailWord_6095395).sum := by decide
  have hdescent : baseEnd_6095395 < baseStart_6095395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095404 : List Nat := [2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 5]
def baseStart_6095404 : Nat := 118140960795 + 6095404 * 2 ^ 59
def prefixEnd_6095404 : Nat := 4983230072969 + 3 ^ 40 * 6095404 * 2
def baseEnd_6095404 : Nat := 3129872035338174937517753

theorem tailTrace_6095404 : CollatzResearch.WordTrace tailWord_6095404 prefixEnd_6095404 3129872035338174937517753 := by
  unfold tailWord_6095404
  simp only [CollatzResearch.WordTrace]
  refine ⟨111158824004699897484550633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148211765339599863312734177 111158824004699897484550633)
  ·
    refine ⟨83369118003524923113412975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111158824004699897484550633 83369118003524923113412975)
    ·
      refine ⟨125053677005287384670119463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83369118003524923113412975 125053677005287384670119463)
      ·
        refine ⟨187580515507931077005179195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125053677005287384670119463 187580515507931077005179195)
        ·
          refine ⟨281370773261896615507768793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187580515507931077005179195 281370773261896615507768793)
          ·
            refine ⟨211028079946422461630826595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281370773261896615507768793 211028079946422461630826595)
            ·
              refine ⟨316542119919633692446239893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211028079946422461630826595 316542119919633692446239893)
              ·
                refine ⟨14837911871232829333417495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 316542119919633692446239893 14837911871232829333417495)
                ·
                  refine ⟨22256867806849244000126243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14837911871232829333417495 22256867806849244000126243)
                  ·
                    refine ⟨33385301710273866000189365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22256867806849244000126243 33385301710273866000189365)
                    ·
                      refine ⟨3129872035338174937517753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33385301710273866000189365 3129872035338174937517753)
                      ·
                        rfl

theorem cell23_6095404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 5].length) (baseStart_6095404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095404 prefixEnd_6095404 := by exact prefixLift 6095404
  have htrace : WordTrace (prefixWord ++ tailWord_6095404) baseStart_6095404 baseEnd_6095404 := by
    simpa [prefixWord, tailWord_6095404, baseEnd_6095404] using wordTrace_append hprefix tailTrace_6095404
  have hstable : (prefixWord ++ tailWord_6095404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095404).length < 2 ^ (prefixWord ++ tailWord_6095404).sum := by decide
  have hdescent : baseEnd_6095404 < baseStart_6095404 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095411 : List Nat := [1, 1, 1, 2, 4, 2, 1, 5, 2, 4]
def baseStart_6095411 : Nat := 118140960795 + 6095411 * 2 ^ 59
def prefixEnd_6095411 : Nat := 4983230072969 + 3 ^ 40 * 6095411 * 2
def baseEnd_6095411 : Nat := 1043291876567585470043407

theorem tailTrace_6095411 : CollatzResearch.WordTrace tailWord_6095411 prefixEnd_6095411 1043291876567585470043407 := by
  unfold tailWord_6095411
  simp only [CollatzResearch.WordTrace]
  refine ⟨222317903320374435164606087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148211935546916290109737391 222317903320374435164606087)
  ·
    refine ⟨333476854980561652746909131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222317903320374435164606087 333476854980561652746909131)
    ·
      refine ⟨500215282470842479120363697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333476854980561652746909131 500215282470842479120363697)
      ·
        refine ⟨375161461853131859340272773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 500215282470842479120363697 375161461853131859340272773)
        ·
          refine ⟨70342774097462223626301145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 375161461853131859340272773 70342774097462223626301145)
          ·
            refine ⟨52757080573096667719725859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70342774097462223626301145 52757080573096667719725859)
            ·
              refine ⟨79135620859645001579588789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52757080573096667719725859 79135620859645001579588789)
              ·
                refine ⟨7418964455591718898086449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79135620859645001579588789 7418964455591718898086449)
                ·
                  refine ⟨5564223341693789173564837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7418964455591718898086449 5564223341693789173564837)
                  ·
                    refine ⟨1043291876567585470043407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5564223341693789173564837 1043291876567585470043407)
                    ·
                      rfl

theorem cell23_6095411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 5, 2, 4].length) (baseStart_6095411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095411 prefixEnd_6095411 := by exact prefixLift 6095411
  have htrace : WordTrace (prefixWord ++ tailWord_6095411) baseStart_6095411 baseEnd_6095411 := by
    simpa [prefixWord, tailWord_6095411, baseEnd_6095411] using wordTrace_append hprefix tailTrace_6095411
  have hstable : (prefixWord ++ tailWord_6095411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095411).length < 2 ^ (prefixWord ++ tailWord_6095411).sum := by decide
  have hdescent : baseEnd_6095411 < baseStart_6095411 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095412 : List Nat := [2, 5, 1, 3, 1, 1, 1, 2, 3, 1, 3]
def baseStart_6095412 : Nat := 118140960795 + 6095412 * 2 ^ 59
def prefixEnd_6095412 : Nat := 4983230072969 + 3 ^ 40 * 6095412 * 2
def baseEnd_6095412 : Nat := 3129876143183410906217717

theorem tailTrace_6095412 : CollatzResearch.WordTrace tailWord_6095412 prefixEnd_6095412 3129876143183410906217717 := by
  unfold tailWord_6095412
  simp only [CollatzResearch.WordTrace]
  refine ⟨111158969896685406167696245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148211959862247208223594993 111158969896685406167696245)
  ·
    refine ⟨10421153427814256828221523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111158969896685406167696245 10421153427814256828221523)
    ·
      refine ⟨15631730141721385242332285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10421153427814256828221523 15631730141721385242332285)
      ·
        refine ⟨5861898803145519465874607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15631730141721385242332285 5861898803145519465874607)
        ·
          refine ⟨8792848204718279198811911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5861898803145519465874607 8792848204718279198811911)
          ·
            refine ⟨13189272307077418798217867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8792848204718279198811911 13189272307077418798217867)
            ·
              refine ⟨19783908460616128197326801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13189272307077418798217867 19783908460616128197326801)
              ·
                refine ⟨14837931345462096147995101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19783908460616128197326801 14837931345462096147995101)
                ·
                  refine ⟨5564224254548286055498163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14837931345462096147995101 5564224254548286055498163)
                  ·
                    refine ⟨8346336381822429083247245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5564224254548286055498163 8346336381822429083247245)
                    ·
                      refine ⟨3129876143183410906217717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8346336381822429083247245 3129876143183410906217717)
                      ·
                        rfl

theorem cell23_6095412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_6095412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095412 prefixEnd_6095412 := by exact prefixLift 6095412
  have htrace : WordTrace (prefixWord ++ tailWord_6095412) baseStart_6095412 baseEnd_6095412 := by
    simpa [prefixWord, tailWord_6095412, baseEnd_6095412] using wordTrace_append hprefix tailTrace_6095412
  have hstable : (prefixWord ++ tailWord_6095412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095412).length < 2 ^ (prefixWord ++ tailWord_6095412).sum := by decide
  have hdescent : baseEnd_6095412 < baseStart_6095412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095418 : List Nat := [3, 1, 1, 1, 3, 3, 1, 1, 5, 2, 2]
def baseStart_6095418 : Nat := 118140960795 + 6095418 * 2 ^ 59
def prefixEnd_6095418 : Nat := 4983230072969 + 3 ^ 40 * 6095418 * 2
def baseEnd_6095418 : Nat := 3129879224067337882742689

theorem tailTrace_6095418 : CollatzResearch.WordTrace tailWord_6095418 prefixEnd_6095418 3129879224067337882742689 := by
  unfold tailWord_6095418
  simp only [CollatzResearch.WordTrace]
  refine ⟨55579539657837268840027727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148212105754232716906740605 55579539657837268840027727)
  ·
    refine ⟨83369309486755903260041591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55579539657837268840027727 83369309486755903260041591)
    ·
      refine ⟨125053964230133854890062387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83369309486755903260041591 125053964230133854890062387)
      ·
        refine ⟨187580946345200782335093581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125053964230133854890062387 187580946345200782335093581)
        ·
          refine ⟨70342854879450293375660093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187580946345200782335093581 70342854879450293375660093)
          ·
            refine ⟨26378570579793860015872535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70342854879450293375660093 26378570579793860015872535)
            ·
              refine ⟨39567855869690790023808803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26378570579793860015872535 39567855869690790023808803)
              ·
                refine ⟨59351783804536185035713205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39567855869690790023808803 59351783804536185035713205)
                ·
                  refine ⟨5564229731675267347098113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59351783804536185035713205 5564229731675267347098113)
                  ·
                    refine ⟨4173172298756450510323585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5564229731675267347098113 4173172298756450510323585)
                    ·
                      refine ⟨3129879224067337882742689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4173172298756450510323585 3129879224067337882742689)
                      ·
                        rfl

theorem cell23_6095418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 5, 2, 2].length) (baseStart_6095418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095418 prefixEnd_6095418 := by exact prefixLift 6095418
  have htrace : WordTrace (prefixWord ++ tailWord_6095418) baseStart_6095418 baseEnd_6095418 := by
    simpa [prefixWord, tailWord_6095418, baseEnd_6095418] using wordTrace_append hprefix tailTrace_6095418
  have hstable : (prefixWord ++ tailWord_6095418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095418).length < 2 ^ (prefixWord ++ tailWord_6095418).sum := by decide
  have hdescent : baseEnd_6095418 < baseStart_6095418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095431 : List Nat := [1, 1, 4, 1, 4, 1, 2, 2, 1, 2, 4]
def baseStart_6095431 : Nat := 118140960795 + 6095431 * 2 ^ 59
def prefixEnd_6095431 : Nat := 4983230072969 + 3 ^ 40 * 6095431 * 2
def baseEnd_6095431 : Nat := 3129885899315846331880129

theorem tailTrace_6095431 : CollatzResearch.WordTrace tailWord_6095431 prefixEnd_6095431 3129885899315846331880129 := by
  unfold tailWord_6095431
  simp only [CollatzResearch.WordTrace]
  refine ⟨222318632780301978580334147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148212421853534652386889431 222318632780301978580334147)
  ·
    refine ⟨333477949170452967870501221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222318632780301978580334147 333477949170452967870501221)
    ·
      refine ⟨62527115469459931475718979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 333477949170452967870501221 62527115469459931475718979)
      ·
        refine ⟨93790673204189897213578469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62527115469459931475718979 93790673204189897213578469)
        ·
          refine ⟨17585751225785605727545963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93790673204189897213578469 17585751225785605727545963)
          ·
            refine ⟨26378626838678408591318945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17585751225785605727545963 26378626838678408591318945)
            ·
              refine ⟨19783970129008806443489209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26378626838678408591318945 19783970129008806443489209)
              ·
                refine ⟨14837977596756604832616907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19783970129008806443489209 14837977596756604832616907)
                ·
                  refine ⟨22256966395134907248925361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14837977596756604832616907 22256966395134907248925361)
                  ·
                    refine ⟨16692724796351180436694021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22256966395134907248925361 16692724796351180436694021)
                    ·
                      refine ⟨3129885899315846331880129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16692724796351180436694021 3129885899315846331880129)
                      ·
                        rfl

theorem cell23_6095431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_6095431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095431 prefixEnd_6095431 := by exact prefixLift 6095431
  have htrace : WordTrace (prefixWord ++ tailWord_6095431) baseStart_6095431 baseEnd_6095431 := by
    simpa [prefixWord, tailWord_6095431, baseEnd_6095431] using wordTrace_append hprefix tailTrace_6095431
  have hstable : (prefixWord ++ tailWord_6095431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095431).length < 2 ^ (prefixWord ++ tailWord_6095431).sum := by decide
  have hdescent : baseEnd_6095431 < baseStart_6095431 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095435 : List Nat := [1, 1, 1, 1, 3, 1, 5, 5, 1, 2, 2]
def baseStart_6095435 : Nat := 118140960795 + 6095435 * 2 ^ 59
def prefixEnd_6095435 : Nat := 4983230072969 + 3 ^ 40 * 6095435 * 2
def baseEnd_6095435 : Nat := 3129887953238464316230111

theorem tailTrace_6095435 : CollatzResearch.WordTrace tailWord_6095435 prefixEnd_6095435 3129887953238464316230111 := by
  unfold tailWord_6095435
  simp only [CollatzResearch.WordTrace]
  refine ⟨222318778672287487263479759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148212519114858324842319839 222318778672287487263479759)
  ·
    refine ⟨333478168008431230895219639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222318778672287487263479759 333478168008431230895219639)
    ·
      refine ⟨500217252012646846342829459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333478168008431230895219639 500217252012646846342829459)
      ·
        refine ⟨750325878018970269514244189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500217252012646846342829459 750325878018970269514244189)
        ·
          refine ⟨281372204257113851067841571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 750325878018970269514244189 281372204257113851067841571)
          ·
            refine ⟨422058306385670776601762357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281372204257113851067841571 422058306385670776601762357)
            ·
              refine ⟨39567966223656635306415221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 422058306385670776601762357 39567966223656635306415221)
              ·
                refine ⟨3709496833467809559976427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39567966223656635306415221 3709496833467809559976427)
                ·
                  refine ⟨5564245250201714339964641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3709496833467809559976427 5564245250201714339964641)
                  ·
                    refine ⟨4173183937651285754973481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5564245250201714339964641 4173183937651285754973481)
                    ·
                      refine ⟨3129887953238464316230111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4173183937651285754973481 3129887953238464316230111)
                      ·
                        rfl

theorem cell23_6095435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 5, 1, 2, 2].length) (baseStart_6095435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095435 prefixEnd_6095435 := by exact prefixLift 6095435
  have htrace : WordTrace (prefixWord ++ tailWord_6095435) baseStart_6095435 baseEnd_6095435 := by
    simpa [prefixWord, tailWord_6095435, baseEnd_6095435] using wordTrace_append hprefix tailTrace_6095435
  have hstable : (prefixWord ++ tailWord_6095435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095435).length < 2 ^ (prefixWord ++ tailWord_6095435).sum := by decide
  have hdescent : baseEnd_6095435 < baseStart_6095435 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095452 : List Nat := [2, 2, 4, 1, 3, 1, 2, 1, 3, 2, 2]
def baseStart_6095452 : Nat := 118140960795 + 6095452 * 2 ^ 59
def prefixEnd_6095452 : Nat := 4983230072969 + 3 ^ 40 * 6095452 * 2
def baseEnd_6095452 : Nat := 3129896682409590749717533

theorem tailTrace_6095452 : CollatzResearch.WordTrace tailWord_6095452 prefixEnd_6095452 3129896682409590749717533 := by
  unfold tailWord_6095452
  simp only [CollatzResearch.WordTrace]
  refine ⟨111159699356612949583424305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148212932475483932777899073 111159699356612949583424305)
  ·
    refine ⟨83369774517459712187568229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111159699356612949583424305 83369774517459712187568229)
    ·
      refine ⟨15631832722023696035169043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83369774517459712187568229 15631832722023696035169043)
      ·
        refine ⟨23447749083035544052753565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15631832722023696035169043 23447749083035544052753565)
        ·
          refine ⟨8792905906138329019782587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23447749083035544052753565 8792905906138329019782587)
          ·
            refine ⟨13189358859207493529673881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8792905906138329019782587 13189358859207493529673881)
            ·
              refine ⟨9892019144405620147255411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13189358859207493529673881 9892019144405620147255411)
              ·
                refine ⟨14838028716608430220883117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9892019144405620147255411 14838028716608430220883117)
                ·
                  refine ⟨5564260768728161332831169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14838028716608430220883117 5564260768728161332831169)
                  ·
                    refine ⟨4173195576546120999623377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5564260768728161332831169 4173195576546120999623377)
                    ·
                      refine ⟨3129896682409590749717533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4173195576546120999623377 3129896682409590749717533)
                      ·
                        rfl

theorem cell23_6095452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_6095452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095452 prefixEnd_6095452 := by exact prefixLift 6095452
  have htrace : WordTrace (prefixWord ++ tailWord_6095452) baseStart_6095452 baseEnd_6095452 := by
    simpa [prefixWord, tailWord_6095452, baseEnd_6095452] using wordTrace_append hprefix tailTrace_6095452
  have hstable : (prefixWord ++ tailWord_6095452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095452).length < 2 ^ (prefixWord ++ tailWord_6095452).sum := by decide
  have hdescent : baseEnd_6095452 < baseStart_6095452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095468 : List Nat := [2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 3]
def baseStart_6095468 : Nat := 118140960795 + 6095468 * 2 ^ 59
def prefixEnd_6095468 : Nat := 4983230072969 + 3 ^ 40 * 6095468 * 2
def baseEnd_6095468 : Nat := 3129904898100062687117459

theorem tailTrace_6095468 : CollatzResearch.WordTrace tailWord_6095468 prefixEnd_6095468 3129904898100062687117459 := by
  unfold tailWord_6095468
  simp only [CollatzResearch.WordTrace]
  refine ⟨111159991140583966949715529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148213321520778622599620705 111159991140583966949715529)
  ·
    refine ⟨83369993355437975212286647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111159991140583966949715529 83369993355437975212286647)
    ·
      refine ⟨125054990033156962818429971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83369993355437975212286647 125054990033156962818429971)
      ·
        refine ⟨187582485049735444227644957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125054990033156962818429971 187582485049735444227644957)
        ·
          refine ⟨70343431893650791585366859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187582485049735444227644957 70343431893650791585366859)
          ·
            refine ⟨105515147840476187378050289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70343431893650791585366859 105515147840476187378050289)
            ·
              refine ⟨79136360880357140533537717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105515147840476187378050289 79136360880357140533537717)
              ·
                refine ⟨7419033832533481925019161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79136360880357140533537717 7419033832533481925019161)
                ·
                  refine ⟨5564275374400111443764371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7419033832533481925019161 5564275374400111443764371)
                  ·
                    refine ⟨8346413061600167165646557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5564275374400111443764371 8346413061600167165646557)
                    ·
                      refine ⟨3129904898100062687117459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8346413061600167165646557 3129904898100062687117459)
                      ·
                        rfl

theorem cell23_6095468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 3].length) (baseStart_6095468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095468 prefixEnd_6095468 := by exact prefixLift 6095468
  have htrace : WordTrace (prefixWord ++ tailWord_6095468) baseStart_6095468 baseEnd_6095468 := by
    simpa [prefixWord, tailWord_6095468, baseEnd_6095468] using wordTrace_append hprefix tailTrace_6095468
  have hstable : (prefixWord ++ tailWord_6095468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095468).length < 2 ^ (prefixWord ++ tailWord_6095468).sum := by decide
  have hdescent : baseEnd_6095468 < baseStart_6095468 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095484 : List Nat := [2, 2, 2, 1, 1, 2, 2, 2, 1, 8]
def baseStart_6095484 : Nat := 118140960795 + 6095484 * 2 ^ 59
def prefixEnd_6095484 : Nat := 4983230072969 + 3 ^ 40 * 6095484 * 2
def baseEnd_6095484 : Nat := 1043304371263511541505795

theorem tailTrace_6095484 : CollatzResearch.WordTrace tailWord_6095484 prefixEnd_6095484 1043304371263511541505795 := by
  unfold tailWord_6095484
  simp only [CollatzResearch.WordTrace]
  refine ⟨111160282924554984316006753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148213710566073312421342337 111160282924554984316006753)
  ·
    refine ⟨83370212193416238237005065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111160282924554984316006753 83370212193416238237005065)
    ·
      refine ⟨62527659145062178677753799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83370212193416238237005065 62527659145062178677753799)
      ·
        refine ⟨93791488717593268016630699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62527659145062178677753799 93791488717593268016630699)
        ·
          refine ⟨140687233076389902024946049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93791488717593268016630699 140687233076389902024946049)
          ·
            refine ⟨105515424807292426518709537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140687233076389902024946049 105515424807292426518709537)
            ·
              refine ⟨79136568605469319889032153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105515424807292426518709537 79136568605469319889032153)
              ·
                refine ⟨59352426454101989916774115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79136568605469319889032153 59352426454101989916774115)
                ·
                  refine ⟨89028639681152984875161173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59352426454101989916774115 89028639681152984875161173)
                  ·
                    refine ⟨1043304371263511541505795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 89028639681152984875161173 1043304371263511541505795)
                    ·
                      rfl

theorem cell23_6095484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_6095484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095484 prefixEnd_6095484 := by exact prefixLift 6095484
  have htrace : WordTrace (prefixWord ++ tailWord_6095484) baseStart_6095484 baseEnd_6095484 := by
    simpa [prefixWord, tailWord_6095484, baseEnd_6095484] using wordTrace_append hprefix tailTrace_6095484
  have hstable : (prefixWord ++ tailWord_6095484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095484).length < 2 ^ (prefixWord ++ tailWord_6095484).sum := by decide
  have hdescent : baseEnd_6095484 < baseStart_6095484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095511 : List Nat := [1, 1, 3, 3, 2, 1, 2, 1, 2, 4, 3]
def baseStart_6095511 : Nat := 118140960795 + 6095511 * 2 ^ 59
def prefixEnd_6095511 : Nat := 4983230072969 + 3 ^ 40 * 6095511 * 2
def baseEnd_6095511 : Nat := 3129926977768206018879761

theorem tailTrace_6095511 : CollatzResearch.WordTrace tailWord_6095511 prefixEnd_6095511 3129926977768206018879761 := by
  unfold tailWord_6095511
  simp only [CollatzResearch.WordTrace]
  refine ⟨222321550620012152243246387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148214367080008101495497591 222321550620012152243246387)
  ·
    refine ⟨333482325930018228364869581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222321550620012152243246387 333482325930018228364869581)
    ·
      refine ⟨125055872223756835636826093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 333482325930018228364869581 125055872223756835636826093)
      ·
        refine ⟨46895952083908813363809785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125055872223756835636826093 46895952083908813363809785)
        ·
          refine ⟨35171964062931610022857339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46895952083908813363809785 35171964062931610022857339)
          ·
            refine ⟨52757946094397415034286009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35171964062931610022857339 52757946094397415034286009)
            ·
              refine ⟨39568459570798061275714507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52757946094397415034286009 39568459570798061275714507)
              ·
                refine ⟨59352689356197091913571761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39568459570798061275714507 59352689356197091913571761)
                ·
                  refine ⟨44514517017147818935178821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59352689356197091913571761 44514517017147818935178821)
                  ·
                    refine ⟨8346471940715216050346029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44514517017147818935178821 8346471940715216050346029)
                    ·
                      refine ⟨3129926977768206018879761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8346471940715216050346029 3129926977768206018879761)
                      ·
                        rfl

theorem cell23_6095511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_6095511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095511 prefixEnd_6095511 := by exact prefixLift 6095511
  have htrace : WordTrace (prefixWord ++ tailWord_6095511) baseStart_6095511 baseEnd_6095511 := by
    simpa [prefixWord, tailWord_6095511, baseEnd_6095511] using wordTrace_append hprefix tailTrace_6095511
  have hstable : (prefixWord ++ tailWord_6095511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095511).length < 2 ^ (prefixWord ++ tailWord_6095511).sum := by decide
  have hdescent : baseEnd_6095511 < baseStart_6095511 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095548 : List Nat := [2, 2, 2, 3, 1, 1, 2, 5, 5]
def baseStart_6095548 : Nat := 118140960795 + 6095548 * 2 ^ 59
def prefixEnd_6095548 : Nat := 4983230072969 + 3 ^ 40 * 6095548 * 2
def baseEnd_6095548 : Nat := 347771775172491374901899

theorem tailTrace_6095548 : CollatzResearch.WordTrace tailWord_6095548 prefixEnd_6095548 347771775172491374901899 := by
  unfold tailWord_6095548
  simp only [CollatzResearch.WordTrace]
  refine ⟨111161450060439053781171649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148215266747252071708228865 111161450060439053781171649)
  ·
    refine ⟨83371087545329290335878737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111161450060439053781171649 83371087545329290335878737)
    ·
      refine ⟨62528315658996967751909053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83371087545329290335878737 62528315658996967751909053)
      ·
        refine ⟨23448118372123862906965895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62528315658996967751909053 23448118372123862906965895)
        ·
          refine ⟨35172177558185794360448843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23448118372123862906965895 35172177558185794360448843)
          ·
            refine ⟨52758266337278691540673265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35172177558185794360448843 52758266337278691540673265)
            ·
              refine ⟨39568699752959018655504949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52758266337278691540673265 39568699752959018655504949)
              ·
                refine ⟨3709565601839907998953589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39568699752959018655504949 3709565601839907998953589)
                ·
                  refine ⟨347771775172491374901899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3709565601839907998953589 347771775172491374901899)
                  ·
                    rfl

theorem cell23_6095548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 5, 5].length) (baseStart_6095548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095548 prefixEnd_6095548 := by exact prefixLift 6095548
  have htrace : WordTrace (prefixWord ++ tailWord_6095548) baseStart_6095548 baseEnd_6095548 := by
    simpa [prefixWord, tailWord_6095548, baseEnd_6095548] using wordTrace_append hprefix tailTrace_6095548
  have hstable : (prefixWord ++ tailWord_6095548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095548).length < 2 ^ (prefixWord ++ tailWord_6095548).sum := by decide
  have hdescent : baseEnd_6095548 < baseStart_6095548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095598 : List Nat := [4, 1, 2, 1, 1, 4, 1, 1, 1, 3, 4]
def baseStart_6095598 : Nat := 118140960795 + 6095598 * 2 ^ 59
def prefixEnd_6095598 : Nat := 4983230072969 + 3 ^ 40 * 6095598 * 2
def baseEnd_6095598 : Nat := 3129971650585147178491861

theorem tailTrace_6095598 : CollatzResearch.WordTrace tailWord_6095598 prefixEnd_6095598 3129971650585147178491861 := by
  unfold tailWord_6095598
  simp only [CollatzResearch.WordTrace]
  refine ⟨27790590471337120762707931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148216482513797977401108965 27790590471337120762707931)
  ·
    refine ⟨41685885707005681144061897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27790590471337120762707931 41685885707005681144061897)
    ·
      refine ⟨31264414280254260858046423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41685885707005681144061897 31264414280254260858046423)
      ·
        refine ⟨46896621420381391287069635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31264414280254260858046423 46896621420381391287069635)
        ·
          refine ⟨70344932130572086930604453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46896621420381391287069635 70344932130572086930604453)
          ·
            refine ⟨13189674774482266299488335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70344932130572086930604453 13189674774482266299488335)
            ·
              refine ⟨19784512161723399449232503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13189674774482266299488335 19784512161723399449232503)
              ·
                refine ⟨29676768242585099173848755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19784512161723399449232503 29676768242585099173848755)
                ·
                  refine ⟨44515152363877648760773133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29676768242585099173848755 44515152363877648760773133)
                  ·
                    refine ⟨16693182136454118285289925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44515152363877648760773133 16693182136454118285289925)
                    ·
                      refine ⟨3129971650585147178491861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16693182136454118285289925 3129971650585147178491861)
                      ·
                        rfl

theorem cell23_6095598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_6095598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095598 prefixEnd_6095598 := by exact prefixLift 6095598
  have htrace : WordTrace (prefixWord ++ tailWord_6095598) baseStart_6095598 baseEnd_6095598 := by
    simpa [prefixWord, tailWord_6095598, baseEnd_6095598] using wordTrace_append hprefix tailTrace_6095598
  have hstable : (prefixWord ++ tailWord_6095598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095598).length < 2 ^ (prefixWord ++ tailWord_6095598).sum := by decide
  have hdescent : baseEnd_6095598 < baseStart_6095598 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095625 : List Nat := [1, 2, 1, 1, 3, 2, 4, 4, 1, 4]
def baseStart_6095625 : Nat := 118140960795 + 6095625 * 2 ^ 59
def prefixEnd_6095625 : Nat := 4983230072969 + 3 ^ 40 * 6095625 * 2
def baseEnd_6095625 : Nat := 1043328504854272857618079

theorem tailTrace_6095625 : CollatzResearch.WordTrace tailWord_6095625 prefixEnd_6095625 1043328504854272857618079 := by
  unfold tailWord_6095625
  simp only [CollatzResearch.WordTrace]
  refine ⟨222325708541599149712896329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148217139027732766475264219 222325708541599149712896329)
  ·
    refine ⟨166744281406199362284672247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222325708541599149712896329 166744281406199362284672247)
    ·
      refine ⟨250116422109299043427008371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166744281406199362284672247 250116422109299043427008371)
      ·
        refine ⟨375174633163948565140512557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250116422109299043427008371 375174633163948565140512557)
        ·
          refine ⟨140690487436480711927692209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 375174633163948565140512557 140690487436480711927692209)
          ·
            refine ⟨105517865577360533945769157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140690487436480711927692209 105517865577360533945769157)
            ·
              refine ⟨19784599795755100114831717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105517865577360533945769157 19784599795755100114831717)
              ·
                refine ⟨3709612461704081271530947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19784599795755100114831717 3709612461704081271530947)
                ·
                  refine ⟨5564418692556121907296421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3709612461704081271530947 5564418692556121907296421)
                  ·
                    refine ⟨1043328504854272857618079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5564418692556121907296421 1043328504854272857618079)
                    ·
                      rfl

theorem cell23_6095625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 4, 1, 4].length) (baseStart_6095625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095625 prefixEnd_6095625 := by exact prefixLift 6095625
  have htrace : WordTrace (prefixWord ++ tailWord_6095625) baseStart_6095625 baseEnd_6095625 := by
    simpa [prefixWord, tailWord_6095625, baseEnd_6095625] using wordTrace_append hprefix tailTrace_6095625
  have hstable : (prefixWord ++ tailWord_6095625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095625).length < 2 ^ (prefixWord ++ tailWord_6095625).sum := by decide
  have hdescent : baseEnd_6095625 < baseStart_6095625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095688 : List Nat := [2, 1, 3, 1, 1, 3, 2, 2, 3, 1, 4]
def baseStart_6095688 : Nat := 118140960795 + 6095688 * 2 ^ 59
def prefixEnd_6095688 : Nat := 4983230072969 + 3 ^ 40 * 6095688 * 2
def baseEnd_6095688 : Nat := 3130017863844051826366447

theorem tailTrace_6095688 : CollatzResearch.WordTrace tailWord_6095688 prefixEnd_6095688 3130017863844051826366447 := by
  unfold tailWord_6095688
  simp only [CollatzResearch.WordTrace]
  refine ⟨111164003170185455736219859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148218670893580607648293145 111164003170185455736219859)
  ·
    refine ⟨166746004755278183604329789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111164003170185455736219859 166746004755278183604329789)
    ·
      refine ⟨62529751783229318851623671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166746004755278183604329789 62529751783229318851623671)
      ·
        refine ⟨93794627674843978277435507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62529751783229318851623671 93794627674843978277435507)
        ·
          refine ⟨140691941512265967416153261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93794627674843978277435507 140691941512265967416153261)
          ·
            refine ⟨52759478067099737781057473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140691941512265967416153261 52759478067099737781057473)
            ·
              refine ⟨39569608550324803335793105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52759478067099737781057473 39569608550324803335793105)
              ·
                refine ⟨29677206412743602501844829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39569608550324803335793105 29677206412743602501844829)
                ·
                  refine ⟨11128952404778850938191811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29677206412743602501844829 11128952404778850938191811)
                  ·
                    refine ⟨16693428607168276407287717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11128952404778850938191811 16693428607168276407287717)
                    ·
                      refine ⟨3130017863844051826366447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16693428607168276407287717 3130017863844051826366447)
                      ·
                        rfl

theorem cell23_6095688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_6095688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095688 prefixEnd_6095688 := by exact prefixLift 6095688
  have htrace : WordTrace (prefixWord ++ tailWord_6095688) baseStart_6095688 baseEnd_6095688 := by
    simpa [prefixWord, tailWord_6095688, baseEnd_6095688] using wordTrace_append hprefix tailTrace_6095688
  have hstable : (prefixWord ++ tailWord_6095688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095688).length < 2 ^ (prefixWord ++ tailWord_6095688).sum := by decide
  have hdescent : baseEnd_6095688 < baseStart_6095688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095698 : List Nat := [3, 2, 2, 1, 1, 2, 2, 3, 1, 6]
def baseStart_6095698 : Nat := 118140960795 + 6095698 * 2 ^ 59
def prefixEnd_6095698 : Nat := 4983230072969 + 3 ^ 40 * 6095698 * 2
def baseEnd_6095698 : Nat := 1043340999550198929080467

theorem tailTrace_6095698 : CollatzResearch.WordTrace tailWord_6095698 prefixEnd_6095698 1043340999550198929080467 := by
  unfold tailWord_6095698
  simp only [CollatzResearch.WordTrace]
  refine ⟨55582092767583670795075937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148218914046889788786869165 55582092767583670795075937)
  ·
    refine ⟨41686569575687753096306953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55582092767583670795075937 41686569575687753096306953)
    ·
      refine ⟨31264927181765814822230215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41686569575687753096306953 31264927181765814822230215)
      ·
        refine ⟨46897390772648722233345323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31264927181765814822230215 46897390772648722233345323)
        ·
          refine ⟨70346086158973083350017985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46897390772648722233345323 70346086158973083350017985)
          ·
            refine ⟨52759564619229812512513489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70346086158973083350017985 52759564619229812512513489)
            ·
              refine ⟨39569673464422359384385117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52759564619229812512513489 39569673464422359384385117)
              ·
                refine ⟨14838627549158384769144419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39569673464422359384385117 14838627549158384769144419)
                ·
                  refine ⟨22257941323737577153716629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14838627549158384769144419 22257941323737577153716629)
                  ·
                    refine ⟨1043340999550198929080467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22257941323737577153716629 1043340999550198929080467)
                    ·
                      rfl

theorem cell23_6095698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_6095698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095698 prefixEnd_6095698 := by exact prefixLift 6095698
  have htrace : WordTrace (prefixWord ++ tailWord_6095698) baseStart_6095698 baseEnd_6095698 := by
    simpa [prefixWord, tailWord_6095698, baseEnd_6095698] using wordTrace_append hprefix tailTrace_6095698
  have hstable : (prefixWord ++ tailWord_6095698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095698).length < 2 ^ (prefixWord ++ tailWord_6095698).sum := by decide
  have hdescent : baseEnd_6095698 < baseStart_6095698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095705 : List Nat := [1, 2, 1, 2, 2, 4, 3, 2, 1, 1, 4]
def baseStart_6095705 : Nat := 118140960795 + 6095705 * 2 ^ 59
def prefixEnd_6095705 : Nat := 4983230072969 + 3 ^ 40 * 6095705 * 2
def baseEnd_6095705 : Nat := 3130026593015178259853869

theorem tailTrace_6095705 : CollatzResearch.WordTrace tailWord_6095705 prefixEnd_6095705 3130026593015178259853869 := by
  unfold tailWord_6095705
  simp only [CollatzResearch.WordTrace]
  refine ⟨222328626381309323375808569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148219084254206215583872379 222328626381309323375808569)
  ·
    refine ⟨166746469785981992531856427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222328626381309323375808569 166746469785981992531856427)
    ·
      refine ⟨250119704678972988797784641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166746469785981992531856427 250119704678972988797784641)
      ·
        refine ⟨187589778509229741598338481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250119704678972988797784641 187589778509229741598338481)
        ·
          refine ⟨140692333881922306198753861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187589778509229741598338481 140692333881922306198753861)
          ·
            refine ⟨26379812602860432412266349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140692333881922306198753861 26379812602860432412266349)
            ·
              refine ⟨9892429726072662154599881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26379812602860432412266349 9892429726072662154599881)
              ·
                refine ⟨7419322294554496615949911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9892429726072662154599881 7419322294554496615949911)
                ·
                  refine ⟨11128983441831744923924867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7419322294554496615949911 11128983441831744923924867)
                  ·
                    refine ⟨16693475162747617385887301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11128983441831744923924867 16693475162747617385887301)
                    ·
                      refine ⟨3130026593015178259853869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16693475162747617385887301 3130026593015178259853869)
                      ·
                        rfl

theorem cell23_6095705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 2, 1, 1, 4].length) (baseStart_6095705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095705 prefixEnd_6095705 := by exact prefixLift 6095705
  have htrace : WordTrace (prefixWord ++ tailWord_6095705) baseStart_6095705 baseEnd_6095705 := by
    simpa [prefixWord, tailWord_6095705, baseEnd_6095705] using wordTrace_append hprefix tailTrace_6095705
  have hstable : (prefixWord ++ tailWord_6095705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095705).length < 2 ^ (prefixWord ++ tailWord_6095705).sum := by decide
  have hdescent : baseEnd_6095705 < baseStart_6095705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095711 : List Nat := [1, 1, 2, 3, 1, 3, 1, 11]
def baseStart_6095711 : Nat := 118140960795 + 6095711 * 2 ^ 59
def prefixEnd_6095711 : Nat := 4983230072969 + 3 ^ 40 * 6095711 * 2
def baseEnd_6095711 : Nat := 115927024959226119865883

theorem tailTrace_6095711 : CollatzResearch.WordTrace tailWord_6095711 prefixEnd_6095711 115927024959226119865883 := by
  unfold tailWord_6095711
  simp only [CollatzResearch.WordTrace]
  refine ⟨222328845219287586400526987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148219230146191724267017991 222328845219287586400526987)
  ·
    refine ⟨333493267828931379600790481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222328845219287586400526987 333493267828931379600790481)
    ·
      refine ⟨250119950871698534700592861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333493267828931379600790481 250119950871698534700592861)
      ·
        refine ⟨93794981576886950512722323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250119950871698534700592861 93794981576886950512722323)
        ·
          refine ⟨140692472365330425769083485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93794981576886950512722323 140692472365330425769083485)
          ·
            refine ⟨52759677136998909663406307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140692472365330425769083485 52759677136998909663406307)
            ·
              refine ⟨79139515705498364495109461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52759677136998909663406307 79139515705498364495109461)
              ·
                refine ⟨115927024959226119865883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 79139515705498364495109461 115927024959226119865883)
                ·
                  rfl

theorem cell23_6095711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 11].length) (baseStart_6095711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095711 prefixEnd_6095711 := by exact prefixLift 6095711
  have htrace : WordTrace (prefixWord ++ tailWord_6095711) baseStart_6095711 baseEnd_6095711 := by
    simpa [prefixWord, tailWord_6095711, baseEnd_6095711] using wordTrace_append hprefix tailTrace_6095711
  have hstable : (prefixWord ++ tailWord_6095711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095711).length < 2 ^ (prefixWord ++ tailWord_6095711).sum := by decide
  have hdescent : baseEnd_6095711 < baseStart_6095711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095738 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 5, 3, 3]
def baseStart_6095738 : Nat := 118140960795 + 6095738 * 2 ^ 59
def prefixEnd_6095738 : Nat := 4983230072969 + 3 ^ 40 * 6095738 * 2
def baseEnd_6095738 : Nat := 3130043537876776630741217

theorem tailTrace_6095738 : CollatzResearch.WordTrace tailWord_6095738 prefixEnd_6095738 3130043537876776630741217 := by
  unfold tailWord_6095738
  simp only [CollatzResearch.WordTrace]
  refine ⟨55582457497547442502939967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148219886660126513341173245 55582457497547442502939967)
  ·
    refine ⟨83373686246321163754409951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55582457497547442502939967 83373686246321163754409951)
    ·
      refine ⟨125060529369481745631614927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83373686246321163754409951 125060529369481745631614927)
      ·
        refine ⟨187590794054222618447422391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125060529369481745631614927 187590794054222618447422391)
        ·
          refine ⟨281386191081333927671133587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187590794054222618447422391 281386191081333927671133587)
          ·
            refine ⟨422079286622000891506700381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281386191081333927671133587 422079286622000891506700381)
            ·
              refine ⟨158279732483250334315012643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 422079286622000891506700381 158279732483250334315012643)
              ·
                refine ⟨237419598724875501472518965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158279732483250334315012643 237419598724875501472518965)
                ·
                  refine ⟨22258087380457078263048653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 237419598724875501472518965 22258087380457078263048653)
                  ·
                    refine ⟨8346782767671404348643245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22258087380457078263048653 8346782767671404348643245)
                    ·
                      refine ⟨3130043537876776630741217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8346782767671404348643245 3130043537876776630741217)
                      ·
                        rfl

theorem cell23_6095738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 5, 3, 3].length) (baseStart_6095738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095738 prefixEnd_6095738 := by exact prefixLift 6095738
  have htrace : WordTrace (prefixWord ++ tailWord_6095738) baseStart_6095738 baseEnd_6095738 := by
    simpa [prefixWord, tailWord_6095738, baseEnd_6095738] using wordTrace_append hprefix tailTrace_6095738
  have hstable : (prefixWord ++ tailWord_6095738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095738).length < 2 ^ (prefixWord ++ tailWord_6095738).sum := by decide
  have hdescent : baseEnd_6095738 < baseStart_6095738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095762 : List Nat := [3, 2, 3, 2, 2, 1, 3, 7]
def baseStart_6095762 : Nat := 118140960795 + 6095762 * 2 ^ 59
def prefixEnd_6095762 : Nat := 4983230072969 + 3 ^ 40 * 6095762 * 2
def baseEnd_6095762 : Nat := 115927994867129056920041

theorem tailTrace_6095762 : CollatzResearch.WordTrace tailWord_6095762 prefixEnd_6095762 115927994867129056920041 := by
  unfold tailWord_6095762
  simp only [CollatzResearch.WordTrace]
  refine ⟨55582676335525705527658385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148220470228068548073755693 55582676335525705527658385)
  ·
    refine ⟨41687007251644279145743789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55582676335525705527658385 41687007251644279145743789)
    ·
      refine ⟨15632627719366604679653921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41687007251644279145743789 15632627719366604679653921)
      ·
        refine ⟨11724470789524953509740441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15632627719366604679653921 11724470789524953509740441)
        ·
          refine ⟨8793353092143715132305331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11724470789524953509740441 8793353092143715132305331)
          ·
            refine ⟨13190029638215572698457997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8793353092143715132305331 13190029638215572698457997)
            ·
              refine ⟨4946261114330839761921749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13190029638215572698457997 4946261114330839761921749)
              ·
                refine ⟨115927994867129056920041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4946261114330839761921749 115927994867129056920041)
                ·
                  rfl

theorem cell23_6095762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 7].length) (baseStart_6095762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095762 prefixEnd_6095762 := by exact prefixLift 6095762
  have htrace : WordTrace (prefixWord ++ tailWord_6095762) baseStart_6095762 baseEnd_6095762 := by
    simpa [prefixWord, tailWord_6095762, baseEnd_6095762] using wordTrace_append hprefix tailTrace_6095762
  have hstable : (prefixWord ++ tailWord_6095762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095762).length < 2 ^ (prefixWord ++ tailWord_6095762).sum := by decide
  have hdescent : baseEnd_6095762 < baseStart_6095762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095882 : List Nat := [3, 1, 2, 2, 3, 2, 2, 1, 2, 5]
def baseStart_6095882 : Nat := 118140960795 + 6095882 * 2 ^ 59
def prefixEnd_6095882 : Nat := 4983230072969 + 3 ^ 40 * 6095882 * 2
def baseEnd_6095882 : Nat := 1043372493030341355780185

theorem tailTrace_6095882 : CollatzResearch.WordTrace tailWord_6095882 prefixEnd_6095882 1043372493030341355780185 := by
  unfold tailWord_6095882
  simp only [CollatzResearch.WordTrace]
  refine ⟨55583770525417020651250475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148223388067778721736667933 55583770525417020651250475)
  ·
    refine ⟨83375655788125530976875713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55583770525417020651250475 83375655788125530976875713)
    ·
      refine ⟨62531741841094148232656785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83375655788125530976875713 62531741841094148232656785)
      ·
        refine ⟨46898806380820611174492589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62531741841094148232656785 46898806380820611174492589)
        ·
          refine ⟨17587052392807729190434721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46898806380820611174492589 17587052392807729190434721)
          ·
            refine ⟨13190289294605796892826041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17587052392807729190434721 13190289294605796892826041)
            ·
              refine ⟨9892716970954347669619531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13190289294605796892826041 9892716970954347669619531)
              ·
                refine ⟨14839075456431521504429297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9892716970954347669619531 14839075456431521504429297)
                ·
                  refine ⟨11129306592323641128321973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14839075456431521504429297 11129306592323641128321973)
                  ·
                    refine ⟨1043372493030341355780185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11129306592323641128321973 1043372493030341355780185)
                    ·
                      rfl

theorem cell23_6095882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 2, 5].length) (baseStart_6095882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095882 prefixEnd_6095882 := by exact prefixLift 6095882
  have htrace : WordTrace (prefixWord ++ tailWord_6095882) baseStart_6095882 baseEnd_6095882 := by
    simpa [prefixWord, tailWord_6095882, baseEnd_6095882] using wordTrace_append hprefix tailTrace_6095882
  have hstable : (prefixWord ++ tailWord_6095882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095882).length < 2 ^ (prefixWord ++ tailWord_6095882).sum := by decide
  have hdescent : baseEnd_6095882 < baseStart_6095882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095888 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 5]
def baseStart_6095888 : Nat := 118140960795 + 6095888 * 2 ^ 59
def prefixEnd_6095888 : Nat := 4983230072969 + 3 ^ 40 * 6095888 * 2
def baseEnd_6095888 : Nat := 3130120559974951043865527

theorem tailTrace_6095888 : CollatzResearch.WordTrace tailWord_6095888 prefixEnd_6095888 3130120559974951043865527 := by
  unfold tailWord_6095888
  simp only [CollatzResearch.WordTrace]
  refine ⟨111167650469823172814860159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148223533959764230419813545 111167650469823172814860159)
  ·
    refine ⟨166751475704734759222290239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111167650469823172814860159 166751475704734759222290239)
    ·
      refine ⟨250127213557102138833435359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166751475704734759222290239 250127213557102138833435359)
      ·
        refine ⟨375190820335653208250153039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250127213557102138833435359 375190820335653208250153039)
        ·
          refine ⟨562786230503479812375229559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375190820335653208250153039 562786230503479812375229559)
          ·
            refine ⟨844179345755219718562844339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 562786230503479812375229559 844179345755219718562844339)
            ·
              refine ⟨1266269018632829577844266509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 844179345755219718562844339 1266269018632829577844266509)
              ·
                refine ⟨474850881987311091691599941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1266269018632829577844266509 474850881987311091691599941)
                ·
                  refine ⟨89034540372620829692174989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 474850881987311091691599941 89034540372620829692174989)
                  ·
                    refine ⟨33387952639732811134565621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89034540372620829692174989 33387952639732811134565621)
                    ·
                      refine ⟨3130120559974951043865527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33387952639732811134565621 3130120559974951043865527)
                      ·
                        rfl

theorem cell23_6095888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 5].length) (baseStart_6095888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095888 prefixEnd_6095888 := by exact prefixLift 6095888
  have htrace : WordTrace (prefixWord ++ tailWord_6095888) baseStart_6095888 baseEnd_6095888 := by
    simpa [prefixWord, tailWord_6095888, baseEnd_6095888] using wordTrace_append hprefix tailTrace_6095888
  have hstable : (prefixWord ++ tailWord_6095888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095888).length < 2 ^ (prefixWord ++ tailWord_6095888).sum := by decide
  have hdescent : baseEnd_6095888 < baseStart_6095888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095976 : List Nat := [2, 1, 4, 4, 1, 1, 3, 1, 6]
def baseStart_6095976 : Nat := 118140960795 + 6095976 * 2 ^ 59
def prefixEnd_6095976 : Nat := 4983230072969 + 3 ^ 40 * 6095976 * 2
def baseEnd_6095976 : Nat := 347796194030282966618347

theorem tailTrace_6095976 : CollatzResearch.WordTrace tailWord_6095976 prefixEnd_6095976 347796194030282966618347 := by
  unfold tailWord_6095976
  simp only [CollatzResearch.WordTrace]
  refine ⟨111169255281663768329461891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148225673708885024439282521 111169255281663768329461891)
  ·
    refine ⟨166753882922495652494192837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111169255281663768329461891 166753882922495652494192837)
    ·
      refine ⟨31266353047967934842661157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166753882922495652494192837 31266353047967934842661157)
      ·
        refine ⟨5862441196493987782998967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31266353047967934842661157 5862441196493987782998967)
        ·
          refine ⟨8793661794740981674498451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5862441196493987782998967 8793661794740981674498451)
          ·
            refine ⟨13190492692111472511747677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8793661794740981674498451 13190492692111472511747677)
            ·
              refine ⟨4946434759541802191905379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13190492692111472511747677 4946434759541802191905379)
              ·
                refine ⟨7419652139312703287858069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4946434759541802191905379 7419652139312703287858069)
                ·
                  refine ⟨347796194030282966618347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7419652139312703287858069 347796194030282966618347)
                  ·
                    rfl

theorem cell23_6095976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 1, 6].length) (baseStart_6095976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095976 prefixEnd_6095976 := by exact prefixLift 6095976
  have htrace : WordTrace (prefixWord ++ tailWord_6095976) baseStart_6095976 baseEnd_6095976 := by
    simpa [prefixWord, tailWord_6095976, baseEnd_6095976] using wordTrace_append hprefix tailTrace_6095976
  have hstable : (prefixWord ++ tailWord_6095976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095976).length < 2 ^ (prefixWord ++ tailWord_6095976).sum := by decide
  have hdescent : baseEnd_6095976 < baseStart_6095976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095985 : List Nat := [1, 2, 2, 2, 1, 1, 2, 5, 1, 6]
def baseStart_6095985 : Nat := 118140960795 + 6095985 * 2 ^ 59
def prefixEnd_6095985 : Nat := 4983230072969 + 3 ^ 40 * 6095985 * 2
def baseEnd_6095985 : Nat := 1043390122532812388117527

theorem tailTrace_6095985 : CollatzResearch.WordTrace tailWord_6095985 prefixEnd_6095985 1043390122532812388117527 := by
  unfold tailWord_6095985
  simp only [CollatzResearch.WordTrace]
  refine ⟨222338838820294931196001409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148225892546863287464000939 222338838820294931196001409)
  ·
    refine ⟨166754129115221198397001057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222338838820294931196001409 166754129115221198397001057)
    ·
      refine ⟨125065596836415898797750793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166754129115221198397001057 125065596836415898797750793)
      ·
        refine ⟨93799197627311924098313095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125065596836415898797750793 93799197627311924098313095)
        ·
          refine ⟨140698796440967886147469643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93799197627311924098313095 140698796440967886147469643)
          ·
            refine ⟨211048194661451829221204465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140698796440967886147469643 211048194661451829221204465)
            ·
              refine ⟨158286145996088871915903349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211048194661451829221204465 158286145996088871915903349)
              ·
                refine ⟨14839326187133331742115939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 158286145996088871915903349 14839326187133331742115939)
                ·
                  refine ⟨22258989280699997613173909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14839326187133331742115939 22258989280699997613173909)
                  ·
                    refine ⟨1043390122532812388117527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22258989280699997613173909 1043390122532812388117527)
                    ·
                      rfl

theorem cell23_6095985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 6].length) (baseStart_6095985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095985 prefixEnd_6095985 := by exact prefixLift 6095985
  have htrace : WordTrace (prefixWord ++ tailWord_6095985) baseStart_6095985 baseEnd_6095985 := by
    simpa [prefixWord, tailWord_6095985, baseEnd_6095985] using wordTrace_append hprefix tailTrace_6095985
  have hstable : (prefixWord ++ tailWord_6095985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095985).length < 2 ^ (prefixWord ++ tailWord_6095985).sum := by decide
  have hdescent : baseEnd_6095985 < baseStart_6095985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095992 : List Nat := [2, 1, 2, 1, 1, 1, 5, 4, 1, 1, 4]
def baseStart_6095992 : Nat := 118140960795 + 6095992 * 2 ^ 59
def prefixEnd_6095992 : Nat := 4983230072969 + 3 ^ 40 * 6095992 * 2
def baseEnd_6095992 : Nat := 3130173961963018636965049

theorem tailTrace_6095992 : CollatzResearch.WordTrace tailWord_6095992 prefixEnd_6095992 3130173961963018636965049 := by
  unfold tailWord_6095992
  simp only [CollatzResearch.WordTrace]
  refine ⟨111169547065634785695753115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148226062754179714261004153 111169547065634785695753115)
  ·
    refine ⟨166754320598452178543629673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111169547065634785695753115 166754320598452178543629673)
    ·
      refine ⟨125065740448839133907722255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166754320598452178543629673 125065740448839133907722255)
      ·
        refine ⟨187598610673258700861583383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125065740448839133907722255 187598610673258700861583383)
        ·
          refine ⟨281397916009888051292375075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187598610673258700861583383 281397916009888051292375075)
          ·
            refine ⟨422096874014832076938562613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281397916009888051292375075 422096874014832076938562613)
            ·
              refine ⟨39571581938890507212990245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 422096874014832076938562613 39571581938890507212990245)
              ·
                refine ⟨7419671613541970102435671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39571581938890507212990245 7419671613541970102435671)
                ·
                  refine ⟨11129507420312955153653507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7419671613541970102435671 11129507420312955153653507)
                  ·
                    refine ⟨16694261130469432730480261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11129507420312955153653507 16694261130469432730480261)
                    ·
                      refine ⟨3130173961963018636965049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16694261130469432730480261 3130173961963018636965049)
                      ·
                        rfl

theorem cell23_6095992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 4, 1, 1, 4].length) (baseStart_6095992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095992 prefixEnd_6095992 := by exact prefixLift 6095992
  have htrace : WordTrace (prefixWord ++ tailWord_6095992) baseStart_6095992 baseEnd_6095992 := by
    simpa [prefixWord, tailWord_6095992, baseEnd_6095992] using wordTrace_append hprefix tailTrace_6095992
  have hstable : (prefixWord ++ tailWord_6095992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095992).length < 2 ^ (prefixWord ++ tailWord_6095992).sum := by decide
  have hdescent : baseEnd_6095992 < baseStart_6095992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6095995 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 2, 6, 3]
def baseStart_6095995 : Nat := 118140960795 + 6095995 * 2 ^ 59
def prefixEnd_6095995 : Nat := 4983230072969 + 3 ^ 40 * 6095995 * 2
def baseEnd_6095995 : Nat := 3130175502404982125227535

theorem tailTrace_6095995 : CollatzResearch.WordTrace tailWord_6095995 prefixEnd_6095995 3130175502404982125227535 := by
  unfold tailWord_6095995
  simp only [CollatzResearch.WordTrace]
  refine ⟨222339203550258702903865439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148226135700172468602576959 222339203550258702903865439)
  ·
    refine ⟨333508805325388054355798159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222339203550258702903865439 333508805325388054355798159)
    ·
      refine ⟨500263207988082081533697239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333508805325388054355798159 500263207988082081533697239)
      ·
        refine ⟨750394811982123122300545859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500263207988082081533697239 750394811982123122300545859)
        ·
          refine ⟨1125592217973184683450818789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 750394811982123122300545859 1125592217973184683450818789)
          ·
            refine ⟨211048540869972128147028523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1125592217973184683450818789 211048540869972128147028523)
            ·
              refine ⟨316572811304958192220542785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211048540869972128147028523 316572811304958192220542785)
              ·
                refine ⟨237429608478718644165407089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 316572811304958192220542785 237429608478718644165407089)
                ·
                  refine ⟨178072206359038983124055317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 237429608478718644165407089 178072206359038983124055317)
                  ·
                    refine ⟨8347134673079952333940093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 178072206359038983124055317 8347134673079952333940093)
                    ·
                      refine ⟨3130175502404982125227535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8347134673079952333940093 3130175502404982125227535)
                      ·
                        rfl

theorem cell23_6095995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 6, 3].length) (baseStart_6095995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6095995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6095995 prefixEnd_6095995 := by exact prefixLift 6095995
  have htrace : WordTrace (prefixWord ++ tailWord_6095995) baseStart_6095995 baseEnd_6095995 := by
    simpa [prefixWord, tailWord_6095995, baseEnd_6095995] using wordTrace_append hprefix tailTrace_6095995
  have hstable : (prefixWord ++ tailWord_6095995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6095995).length < 2 ^ (prefixWord ++ tailWord_6095995).sum := by decide
  have hdescent : baseEnd_6095995 < baseStart_6095995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6095995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096036 : List Nat := [2, 3, 1, 2, 3, 1, 4, 1, 2, 4]
def baseStart_6096036 : Nat := 118140960795 + 6096036 * 2 ^ 59
def prefixEnd_6096036 : Nat := 4983230072969 + 3 ^ 40 * 6096036 * 2
def baseEnd_6096036 : Nat := 1043398851703938821604949

theorem tailTrace_6096036 : CollatzResearch.WordTrace tailWord_6096036 prefixEnd_6096036 1043398851703938821604949 := by
  unfold tailWord_6096036
  simp only [CollatzResearch.WordTrace]
  refine ⟨111170349471555083453053981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148227132628740111270738641 111170349471555083453053981)
  ·
    refine ⟨41688881051833156294895243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111170349471555083453053981 41688881051833156294895243)
    ·
      refine ⟨62533321577749734442342865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41688881051833156294895243 62533321577749734442342865)
      ·
        refine ⟨46899991183312300831757149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62533321577749734442342865 46899991183312300831757149)
        ·
          refine ⟨17587496693742112811908931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46899991183312300831757149 17587496693742112811908931)
          ·
            refine ⟨26381245040613169217863397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17587496693742112811908931 26381245040613169217863397)
            ·
              refine ⟨4946483445114969228349387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26381245040613169217863397 4946483445114969228349387)
              ·
                refine ⟨7419725167672453842524081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4946483445114969228349387 7419725167672453842524081)
                ·
                  refine ⟨5564793875754340381893061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7419725167672453842524081 5564793875754340381893061)
                  ·
                    refine ⟨1043398851703938821604949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5564793875754340381893061 1043398851703938821604949)
                    ·
                      rfl

theorem cell23_6096036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 1, 2, 4].length) (baseStart_6096036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096036 prefixEnd_6096036 := by exact prefixLift 6096036
  have htrace : WordTrace (prefixWord ++ tailWord_6096036) baseStart_6096036 baseEnd_6096036 := by
    simpa [prefixWord, tailWord_6096036, baseEnd_6096036] using wordTrace_append hprefix tailTrace_6096036
  have hstable : (prefixWord ++ tailWord_6096036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096036).length < 2 ^ (prefixWord ++ tailWord_6096036).sum := by decide
  have hdescent : baseEnd_6096036 < baseStart_6096036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096066 : List Nat := [3, 5, 1, 1, 3, 10]
def baseStart_6096066 : Nat := 118140960795 + 6096066 * 2 ^ 59
def prefixEnd_6096066 : Nat := 4983230072969 + 3 ^ 40 * 6096066 * 2
def baseEnd_6096066 : Nat := 12881530697660293610863

theorem tailTrace_6096066 : CollatzResearch.WordTrace tailWord_6096066 prefixEnd_6096066 12881530697660293610863 := by
  unfold tailWord_6096066
  simp only [CollatzResearch.WordTrace]
  refine ⟨55585448283250370507425013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148227862088667654686466701 55585448283250370507425013)
  ·
    refine ⟨5211135776554722235071095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55585448283250370507425013 5211135776554722235071095)
    ·
      refine ⟨7816703664832083352606643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5211135776554722235071095 7816703664832083352606643)
      ·
        refine ⟨11725055497248125028909965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7816703664832083352606643 11725055497248125028909965)
        ·
          refine ⟨4396895811468046885841237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11725055497248125028909965 4396895811468046885841237)
          ·
            refine ⟨12881530697660293610863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4396895811468046885841237 12881530697660293610863)
            ·
              rfl

theorem cell23_6096066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 10].length) (baseStart_6096066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096066 prefixEnd_6096066 := by exact prefixLift 6096066
  have htrace : WordTrace (prefixWord ++ tailWord_6096066) baseStart_6096066 baseEnd_6096066 := by
    simpa [prefixWord, tailWord_6096066, baseEnd_6096066] using wordTrace_append hprefix tailTrace_6096066
  have hstable : (prefixWord ++ tailWord_6096066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096066).length < 2 ^ (prefixWord ++ tailWord_6096066).sum := by decide
  have hdescent : baseEnd_6096066 < baseStart_6096066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096082 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 1, 5, 4]
def baseStart_6096082 : Nat := 118140960795 + 6096082 * 2 ^ 59
def prefixEnd_6096082 : Nat := 4983230072969 + 3 ^ 40 * 6096082 * 2
def baseEnd_6096082 : Nat := 3130220175221923284839635

theorem tailTrace_6096082 : CollatzResearch.WordTrace tailWord_6096082 prefixEnd_6096082 3130220175221923284839635 := by
  unfold tailWord_6096082
  simp only [CollatzResearch.WordTrace]
  refine ⟨55585594175235879190570625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148228251133962344508188333 55585594175235879190570625)
  ·
    refine ⟨41689195631426909392927969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55585594175235879190570625 41689195631426909392927969)
    ·
      refine ⟨31266896723570182044695977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41689195631426909392927969 31266896723570182044695977)
      ·
        refine ⟨23450172542677636533521983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31266896723570182044695977 23450172542677636533521983)
        ·
          refine ⟨35175258814016454800282975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23450172542677636533521983 35175258814016454800282975)
          ·
            refine ⟨52762888221024682200424463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35175258814016454800282975 52762888221024682200424463)
            ·
              refine ⟨79144332331537023300636695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52762888221024682200424463 79144332331537023300636695)
              ·
                refine ⟨118716498497305534950955043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79144332331537023300636695 118716498497305534950955043)
                ·
                  refine ⟨178074747745958302426432565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118716498497305534950955043 178074747745958302426432565)
                  ·
                    refine ⟨16694507601183590852478053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 178074747745958302426432565 16694507601183590852478053)
                    ·
                      refine ⟨3130220175221923284839635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16694507601183590852478053 3130220175221923284839635)
                      ·
                        rfl

theorem cell23_6096082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_6096082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096082 prefixEnd_6096082 := by exact prefixLift 6096082
  have htrace : WordTrace (prefixWord ++ tailWord_6096082) baseStart_6096082 baseEnd_6096082 := by
    simpa [prefixWord, tailWord_6096082, baseEnd_6096082] using wordTrace_append hprefix tailTrace_6096082
  have hstable : (prefixWord ++ tailWord_6096082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096082).length < 2 ^ (prefixWord ++ tailWord_6096082).sum := by decide
  have hdescent : baseEnd_6096082 < baseStart_6096082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096139 : List Nat := [1, 1, 1, 1, 5, 3, 2, 4, 5]
def baseStart_6096139 : Nat := 118140960795 + 6096139 * 2 ^ 59
def prefixEnd_6096139 : Nat := 4983230072969 + 3 ^ 40 * 6096139 * 2
def baseEnd_6096139 : Nat := 347805493735469951314097

theorem tailTrace_6096139 : CollatzResearch.WordTrace tailWord_6096139 prefixEnd_6096139 347805493735469951314097 := by
  unfold tailWord_6096139
  simp only [CollatzResearch.WordTrace]
  refine ⟨222344455661737015497107471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148229637107824676998071647 222344455661737015497107471)
  ·
    refine ⟨333516683492605523245661207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222344455661737015497107471 333516683492605523245661207)
    ·
      refine ⟨500275025238908284868491811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333516683492605523245661207 500275025238908284868491811)
      ·
        refine ⟨750412537858362427302737717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500275025238908284868491811 750412537858362427302737717)
        ·
          refine ⟨70351175424221477559631661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 750412537858362427302737717 70351175424221477559631661)
          ·
            refine ⟨26381690784083054084861873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70351175424221477559631661 26381690784083054084861873)
            ·
              refine ⟨19786268088062290563646405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26381690784083054084861873 19786268088062290563646405)
              ·
                refine ⟨3709925266511679480683701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19786268088062290563646405 3709925266511679480683701)
                ·
                  refine ⟨347805493735469951314097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3709925266511679480683701 347805493735469951314097)
                  ·
                    rfl

theorem cell23_6096139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 4, 5].length) (baseStart_6096139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096139 prefixEnd_6096139 := by exact prefixLift 6096139
  have htrace : WordTrace (prefixWord ++ tailWord_6096139) baseStart_6096139 baseEnd_6096139 := by
    simpa [prefixWord, tailWord_6096139, baseEnd_6096139] using wordTrace_append hprefix tailTrace_6096139
  have hstable : (prefixWord ++ tailWord_6096139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096139).length < 2 ^ (prefixWord ++ tailWord_6096139).sum := by decide
  have hdescent : baseEnd_6096139 < baseStart_6096139 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096152 : List Nat := [2, 1, 2, 3, 1, 3, 1, 2, 1, 7]
def baseStart_6096152 : Nat := 118140960795 + 6096152 * 2 ^ 59
def prefixEnd_6096152 : Nat := 4983230072969 + 3 ^ 40 * 6096152 * 2
def baseEnd_6096152 : Nat := 1043418706289246003654771

theorem tailTrace_6096152 : CollatzResearch.WordTrace tailWord_6096152 prefixEnd_6096152 1043418706289246003654771 := by
  unfold tailWord_6096152
  simp only [CollatzResearch.WordTrace]
  refine ⟨111172464905344959358665355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148229953207126612478220473 111172464905344959358665355)
  ·
    refine ⟨166758697358017439037998033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111172464905344959358665355 166758697358017439037998033)
    ·
      refine ⟨125069023018513079278498525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166758697358017439037998033 125069023018513079278498525)
      ·
        refine ⟨46900883631942404729436947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125069023018513079278498525 46900883631942404729436947)
        ·
          refine ⟨70351325447913607094155421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46900883631942404729436947 70351325447913607094155421)
          ·
            refine ⟨26381747042967602660308283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70351325447913607094155421 26381747042967602660308283)
            ·
              refine ⟨39572620564451403990462425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26381747042967602660308283 39572620564451403990462425)
              ·
                refine ⟨29679465423338552992846819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39572620564451403990462425 29679465423338552992846819)
                ·
                  refine ⟨44519198135007829489270229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29679465423338552992846819 44519198135007829489270229)
                  ·
                    refine ⟨1043418706289246003654771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44519198135007829489270229 1043418706289246003654771)
                    ·
                      rfl

theorem cell23_6096152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 1, 7].length) (baseStart_6096152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096152 prefixEnd_6096152 := by exact prefixLift 6096152
  have htrace : WordTrace (prefixWord ++ tailWord_6096152) baseStart_6096152 baseEnd_6096152 := by
    simpa [prefixWord, tailWord_6096152, baseEnd_6096152] using wordTrace_append hprefix tailTrace_6096152
  have hstable : (prefixWord ++ tailWord_6096152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096152).length < 2 ^ (prefixWord ++ tailWord_6096152).sum := by decide
  have hdescent : baseEnd_6096152 < baseStart_6096152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096173 : List Nat := [1, 5, 3, 1, 1, 1, 3, 3, 5]
def baseStart_6096173 : Nat := 118140960795 + 6096173 * 2 ^ 59
def prefixEnd_6096173 : Nat := 4983230072969 + 3 ^ 40 * 6096173 * 2
def baseEnd_6096173 : Nat := 347807433551275825422413

theorem tailTrace_6096173 : CollatzResearch.WordTrace tailWord_6096173 prefixEnd_6096173 347807433551275825422413 := by
  unfold tailWord_6096173
  simp only [CollatzResearch.WordTrace]
  refine ⟨222345695743613839303845173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148230463829075892869230115 222345695743613839303845173)
  ·
    refine ⟨20844908975963797434735485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 222345695743613839303845173 20844908975963797434735485)
    ·
      refine ⟨7816840865986424038025807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20844908975963797434735485 7816840865986424038025807)
      ·
        refine ⟨11725261298979636057038711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7816840865986424038025807 11725261298979636057038711)
        ·
          refine ⟨17587891948469454085558067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11725261298979636057038711 17587891948469454085558067)
          ·
            refine ⟨26381837922704181128337101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17587891948469454085558067 26381837922704181128337101)
            ·
              refine ⟨9893189221014067923126413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26381837922704181128337101 9893189221014067923126413)
              ·
                refine ⟨3709945957880275471172405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9893189221014067923126413 3709945957880275471172405)
                ·
                  refine ⟨347807433551275825422413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3709945957880275471172405 347807433551275825422413)
                  ·
                    rfl

theorem cell23_6096173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_6096173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096173 prefixEnd_6096173 := by exact prefixLift 6096173
  have htrace : WordTrace (prefixWord ++ tailWord_6096173) baseStart_6096173 baseEnd_6096173 := by
    simpa [prefixWord, tailWord_6096173, baseEnd_6096173] using wordTrace_append hprefix tailTrace_6096173
  have hstable : (prefixWord ++ tailWord_6096173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096173).length < 2 ^ (prefixWord ++ tailWord_6096173).sum := by decide
  have hdescent : baseEnd_6096173 < baseStart_6096173 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096196 : List Nat := [2, 3, 4, 1, 1, 2, 1, 1, 1, 2, 5]
def baseStart_6096196 : Nat := 118140960795 + 6096196 * 2 ^ 59
def prefixEnd_6096196 : Nat := 4983230072969 + 3 ^ 40 * 6096196 * 2
def baseEnd_6096196 : Nat := 3130278712016535838814111

theorem tailTrace_6096196 : CollatzResearch.WordTrace tailWord_6096196 prefixEnd_6096196 3130278712016535838814111 := by
  unfold tailWord_6096196
  simp only [CollatzResearch.WordTrace]
  refine ⟨111173267311265257115966221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148231023081687009487954961 111173267311265257115966221)
  ·
    refine ⟨41689975241724471418487333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111173267311265257115966221 41689975241724471418487333)
    ·
      refine ⟨7816870357823338390966375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41689975241724471418487333 7816870357823338390966375)
      ·
        refine ⟨11725305536735007586449563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7816870357823338390966375 11725305536735007586449563)
        ·
          refine ⟨17587958305102511379674345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11725305536735007586449563 17587958305102511379674345)
          ·
            refine ⟨13190968728826883534755759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17587958305102511379674345 13190968728826883534755759)
            ·
              refine ⟨19786453093240325302133639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13190968728826883534755759 19786453093240325302133639)
              ·
                refine ⟨29679679639860487953200459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19786453093240325302133639 29679679639860487953200459)
                ·
                  refine ⟨44519519459790731929800689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29679679639860487953200459 44519519459790731929800689)
                  ·
                    refine ⟨33389639594843048947350517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44519519459790731929800689 33389639594843048947350517)
                    ·
                      refine ⟨3130278712016535838814111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33389639594843048947350517 3130278712016535838814111)
                      ·
                        rfl

theorem cell23_6096196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_6096196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096196 prefixEnd_6096196 := by exact prefixLift 6096196
  have htrace : WordTrace (prefixWord ++ tailWord_6096196) baseStart_6096196 baseEnd_6096196 := by
    simpa [prefixWord, tailWord_6096196, baseEnd_6096196] using wordTrace_append hprefix tailTrace_6096196
  have hstable : (prefixWord ++ tailWord_6096196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096196).length < 2 ^ (prefixWord ++ tailWord_6096196).sum := by decide
  have hdescent : baseEnd_6096196 < baseStart_6096196 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096202 : List Nat := [3, 1, 2, 1, 1, 1, 1, 4, 2, 1, 6]
def baseStart_6096202 : Nat := 118140960795 + 6096202 * 2 ^ 59
def prefixEnd_6096202 : Nat := 4983230072969 + 3 ^ 40 * 6096202 * 2
def baseEnd_6096202 : Nat := 3130281792900462815339083

theorem tailTrace_6096202 : CollatzResearch.WordTrace tailWord_6096202 prefixEnd_6096202 3130281792900462815339083 := by
  unfold tailWord_6096202
  simp only [CollatzResearch.WordTrace]
  refine ⟨55586688365127194314162715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148231168973672518171100573 55586688365127194314162715)
  ·
    refine ⟨83380032547690791471244073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55586688365127194314162715 83380032547690791471244073)
    ·
      refine ⟨62535024410768093603433055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83380032547690791471244073 62535024410768093603433055)
      ·
        refine ⟨93802536616152140405149583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62535024410768093603433055 93802536616152140405149583)
        ·
          refine ⟨140703804924228210607724375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93802536616152140405149583 140703804924228210607724375)
          ·
            refine ⟨211055707386342315911586563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140703804924228210607724375 211055707386342315911586563)
            ·
              refine ⟨316583561079513473867379845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211055707386342315911586563 316583561079513473867379845)
              ·
                refine ⟨59359417702408776350133721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 316583561079513473867379845 59359417702408776350133721)
                ·
                  refine ⟨44519563276806582262600291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59359417702408776350133721 44519563276806582262600291)
                  ·
                    refine ⟨66779344915209873393900437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44519563276806582262600291 66779344915209873393900437)
                    ·
                      refine ⟨3130281792900462815339083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66779344915209873393900437 3130281792900462815339083)
                      ·
                        rfl

theorem cell23_6096202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_6096202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096202 prefixEnd_6096202 := by exact prefixLift 6096202
  have htrace : WordTrace (prefixWord ++ tailWord_6096202) baseStart_6096202 baseEnd_6096202 := by
    simpa [prefixWord, tailWord_6096202, baseEnd_6096202] using wordTrace_append hprefix tailTrace_6096202
  have hstable : (prefixWord ++ tailWord_6096202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096202).length < 2 ^ (prefixWord ++ tailWord_6096202).sum := by decide
  have hdescent : baseEnd_6096202 < baseStart_6096202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096209 : List Nat := [1, 2, 2, 1, 4, 1, 1, 2, 4, 2, 3]
def baseStart_6096209 : Nat := 118140960795 + 6096209 * 2 ^ 59
def prefixEnd_6096209 : Nat := 4983230072969 + 3 ^ 40 * 6096209 * 2
def baseEnd_6096209 : Nat := 3130285387265044287951551

theorem tailTrace_6096209 : CollatzResearch.WordTrace tailWord_6096209 prefixEnd_6096209 3130285387265044287951551 := by
  unfold tailWord_6096209
  simp only [CollatzResearch.WordTrace]
  refine ⟨222347008771483417452155681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148231339180988944968103787 222347008771483417452155681)
  ·
    refine ⟨166760256578612563089116761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222347008771483417452155681 166760256578612563089116761)
    ·
      refine ⟨125070192433959422316837571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166760256578612563089116761 125070192433959422316837571)
      ·
        refine ⟨187605288650939133475256357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125070192433959422316837571 187605288650939133475256357)
        ·
          refine ⟨35175991622051087526610567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 187605288650939133475256357 35175991622051087526610567)
          ·
            refine ⟨52763987433076631289915851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35175991622051087526610567 52763987433076631289915851)
            ·
              refine ⟨79145981149614946934873777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52763987433076631289915851 79145981149614946934873777)
              ·
                refine ⟨59359485862211210201155333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79145981149614946934873777 59359485862211210201155333)
                ·
                  refine ⟨11129903599164601912716625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59359485862211210201155333 11129903599164601912716625)
                  ·
                    refine ⟨8347427699373451434537469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11129903599164601912716625 8347427699373451434537469)
                    ·
                      refine ⟨3130285387265044287951551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8347427699373451434537469 3130285387265044287951551)
                      ·
                        rfl

theorem cell23_6096209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 4, 2, 3].length) (baseStart_6096209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096209 prefixEnd_6096209 := by exact prefixLift 6096209
  have htrace : WordTrace (prefixWord ++ tailWord_6096209) baseStart_6096209 baseEnd_6096209 := by
    simpa [prefixWord, tailWord_6096209, baseEnd_6096209] using wordTrace_append hprefix tailTrace_6096209
  have hstable : (prefixWord ++ tailWord_6096209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096209).length < 2 ^ (prefixWord ++ tailWord_6096209).sum := by decide
  have hdescent : baseEnd_6096209 < baseStart_6096209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096259 : List Nat := [1, 1, 1, 3, 5, 1, 1, 2, 3, 5]
def baseStart_6096259 : Nat := 118140960795 + 6096259 * 2 ^ 59
def prefixEnd_6096259 : Nat := 4983230072969 + 3 ^ 40 * 6096259 * 2
def baseEnd_6096259 : Nat := 1043437020432589697442107

theorem tailTrace_6096259 : CollatzResearch.WordTrace tailWord_6096259 prefixEnd_6096259 1043437020432589697442107 := by
  unfold tailWord_6096259
  simp only [CollatzResearch.WordTrace]
  refine ⟨222348832421302275991475831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148232554947534850660983887 222348832421302275991475831)
  ·
    refine ⟨333523248631953413987213747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222348832421302275991475831 333523248631953413987213747)
    ·
      refine ⟨500284872947930120980820621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333523248631953413987213747 500284872947930120980820621)
      ·
        refine ⟨187606827355473795367807733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 500284872947930120980820621 187606827355473795367807733)
        ·
          refine ⟨17588140064575668315731975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 187606827355473795367807733 17588140064575668315731975)
          ·
            refine ⟨26382210096863502473597963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17588140064575668315731975 26382210096863502473597963)
            ·
              refine ⟨39573315145295253710396945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26382210096863502473597963 39573315145295253710396945)
              ·
                refine ⟨29679986358971440282797709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39573315145295253710396945 29679986358971440282797709)
                ·
                  refine ⟨11129994884614290106049141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29679986358971440282797709 11129994884614290106049141)
                  ·
                    refine ⟨1043437020432589697442107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11129994884614290106049141 1043437020432589697442107)
                    ·
                      rfl

theorem cell23_6096259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 3, 5].length) (baseStart_6096259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096259 prefixEnd_6096259 := by exact prefixLift 6096259
  have htrace : WordTrace (prefixWord ++ tailWord_6096259) baseStart_6096259 baseEnd_6096259 := by
    simpa [prefixWord, tailWord_6096259, baseEnd_6096259] using wordTrace_append hprefix tailTrace_6096259
  have hstable : (prefixWord ++ tailWord_6096259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096259).length < 2 ^ (prefixWord ++ tailWord_6096259).sum := by decide
  have hdescent : baseEnd_6096259 < baseStart_6096259 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096276 : List Nat := [2, 4, 2, 1, 2, 1, 2, 1, 3, 5]
def baseStart_6096276 : Nat := 118140960795 + 6096276 * 2 ^ 59
def prefixEnd_6096276 : Nat := 4983230072969 + 3 ^ 40 * 6096276 * 2
def baseEnd_6096276 : Nat := 1043439930156298508604581

theorem tailTrace_6096276 : CollatzResearch.WordTrace tailWord_6096276 prefixEnd_6096276 1043439930156298508604581 := by
  unfold tailWord_6096276
  simp only [CollatzResearch.WordTrace]
  refine ⟨111174726231120343947422341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148232968308160458596563121 111174726231120343947422341)
  ·
    refine ⟨20845261168335064490141689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111174726231120343947422341 20845261168335064490141689)
    ·
      refine ⟨15633945876251298367606267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20845261168335064490141689 15633945876251298367606267)
      ·
        refine ⟨23450918814376947551409401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15633945876251298367606267 23450918814376947551409401)
        ·
          refine ⟨17588189110782710663557051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23450918814376947551409401 17588189110782710663557051)
          ·
            refine ⟨26382283666174065995335577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17588189110782710663557051 26382283666174065995335577)
            ·
              refine ⟨19786712749630549496501683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26382283666174065995335577 19786712749630549496501683)
              ·
                refine ⟨29680069124445824244752525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19786712749630549496501683 29680069124445824244752525)
                ·
                  refine ⟨11130025921667184091782197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29680069124445824244752525 11130025921667184091782197)
                  ·
                    refine ⟨1043439930156298508604581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11130025921667184091782197 1043439930156298508604581)
                    ·
                      rfl

theorem cell23_6096276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_6096276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096276 prefixEnd_6096276 := by exact prefixLift 6096276
  have htrace : WordTrace (prefixWord ++ tailWord_6096276) baseStart_6096276 baseEnd_6096276 := by
    simpa [prefixWord, tailWord_6096276, baseEnd_6096276] using wordTrace_append hprefix tailTrace_6096276
  have hstable : (prefixWord ++ tailWord_6096276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096276).length < 2 ^ (prefixWord ++ tailWord_6096276).sum := by decide
  have hdescent : baseEnd_6096276 < baseStart_6096276 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096290 : List Nat := [3, 3, 1, 2, 1, 2, 1, 5, 1, 1, 3]
def baseStart_6096290 : Nat := 118140960795 + 6096290 * 2 ^ 59
def prefixEnd_6096290 : Nat := 4983230072969 + 3 ^ 40 * 6096290 * 2
def baseEnd_6096290 : Nat := 3130326979198058471038679

theorem tailTrace_6096290 : CollatzResearch.WordTrace tailWord_6096290 prefixEnd_6096290 3130326979198058471038679 := by
  unfold tailWord_6096290
  simp only [CollatzResearch.WordTrace]
  refine ⟨55587490771047492071463581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148233308722793312190569549 55587490771047492071463581)
  ·
    refine ⟨20845309039142809526798843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55587490771047492071463581 20845309039142809526798843)
    ·
      refine ⟨31267963558714214290198265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20845309039142809526798843 31267963558714214290198265)
      ·
        refine ⟨23450972669035660717648699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31267963558714214290198265 23450972669035660717648699)
        ·
          refine ⟨35176459003553491076473049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23450972669035660717648699 35176459003553491076473049)
          ·
            refine ⟨26382344252665118307354787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35176459003553491076473049 26382344252665118307354787)
            ·
              refine ⟨39573516378997677461032181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26382344252665118307354787 39573516378997677461032181)
              ·
                refine ⟨3710017160531032261971767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39573516378997677461032181 3710017160531032261971767)
                ·
                  refine ⟨5565025740796548392957651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3710017160531032261971767 5565025740796548392957651)
                  ·
                    refine ⟨8347538611194822589436477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5565025740796548392957651 8347538611194822589436477)
                    ·
                      refine ⟨3130326979198058471038679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8347538611194822589436477 3130326979198058471038679)
                      ·
                        rfl

theorem cell23_6096290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_6096290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096290 prefixEnd_6096290 := by exact prefixLift 6096290
  have htrace : WordTrace (prefixWord ++ tailWord_6096290) baseStart_6096290 baseEnd_6096290 := by
    simpa [prefixWord, tailWord_6096290, baseEnd_6096290] using wordTrace_append hprefix tailTrace_6096290
  have hstable : (prefixWord ++ tailWord_6096290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096290).length < 2 ^ (prefixWord ++ tailWord_6096290).sum := by decide
  have hdescent : baseEnd_6096290 < baseStart_6096290 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096306 : List Nat := [3, 2, 1, 1, 1, 1, 2, 6, 2, 4]
def baseStart_6096306 : Nat := 118140960795 + 6096306 * 2 ^ 59
def prefixEnd_6096306 : Nat := 4983230072969 + 3 ^ 40 * 6096306 * 2
def baseEnd_6096306 : Nat := 1043445064962843469479535

theorem tailTrace_6096306 : CollatzResearch.WordTrace tailWord_6096306 prefixEnd_6096306 1043445064962843469479535 := by
  unfold tailWord_6096306
  simp only [CollatzResearch.WordTrace]
  refine ⟨55587636663033000754609193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148233697768088002012291181 55587636663033000754609193)
  ·
    refine ⟨41690727497274750565956895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55587636663033000754609193 41690727497274750565956895)
    ·
      refine ⟨62536091245912125848935343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41690727497274750565956895 62536091245912125848935343)
      ·
        refine ⟨93804136868868188773403015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62536091245912125848935343 93804136868868188773403015)
        ·
          refine ⟨140706205303302283160104523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93804136868868188773403015 140706205303302283160104523)
          ·
            refine ⟨211059307954953424740156785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140706205303302283160104523 211059307954953424740156785)
            ·
              refine ⟨158294480966215068555117589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211059307954953424740156785 158294480966215068555117589)
              ·
                refine ⟨7420053795291331338521137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 158294480966215068555117589 7420053795291331338521137)
                ·
                  refine ⟨5565040346468498503890853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7420053795291331338521137 5565040346468498503890853)
                  ·
                    refine ⟨1043445064962843469479535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5565040346468498503890853 1043445064962843469479535)
                    ·
                      rfl

theorem cell23_6096306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 6, 2, 4].length) (baseStart_6096306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096306 prefixEnd_6096306 := by exact prefixLift 6096306
  have htrace : WordTrace (prefixWord ++ tailWord_6096306) baseStart_6096306 baseEnd_6096306 := by
    simpa [prefixWord, tailWord_6096306, baseEnd_6096306] using wordTrace_append hprefix tailTrace_6096306
  have hstable : (prefixWord ++ tailWord_6096306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096306).length < 2 ^ (prefixWord ++ tailWord_6096306).sum := by decide
  have hdescent : baseEnd_6096306 < baseStart_6096306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096380 : List Nat := [2, 2, 2, 1, 2, 1, 6, 1, 2, 1, 3]
def baseStart_6096380 : Nat := 118140960795 + 6096380 * 2 ^ 59
def prefixEnd_6096380 : Nat := 4983230072969 + 3 ^ 40 * 6096380 * 2
def baseEnd_6096380 : Nat := 3130373192456963118913265

theorem tailTrace_6096380 : CollatzResearch.WordTrace tailWord_6096380 prefixEnd_6096380 3130373192456963118913265 := by
  unfold tailWord_6096380
  simp only [CollatzResearch.WordTrace]
  refine ⟨111176622826931956828315297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148235497102575942437753729 111176622826931956828315297)
  ·
    refine ⟨83382467120198967621236473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111176622826931956828315297 83382467120198967621236473)
    ·
      refine ⟨62536850340149225715927355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83382467120198967621236473 62536850340149225715927355)
      ·
        refine ⟨93805275510223838573891033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62536850340149225715927355 93805275510223838573891033)
        ·
          refine ⟨70353956632667878930418275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93805275510223838573891033 70353956632667878930418275)
          ·
            refine ⟨105530934949001818395627413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70353956632667878930418275 105530934949001818395627413)
            ·
              refine ⟨4946762575734460237295035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 105530934949001818395627413 4946762575734460237295035)
              ·
                refine ⟨7420143863601690355942553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4946762575734460237295035 7420143863601690355942553)
                ·
                  refine ⟨5565107897701267766956915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7420143863601690355942553 5565107897701267766956915)
                  ·
                    refine ⟨8347661846551901650435373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5565107897701267766956915 8347661846551901650435373)
                    ·
                      refine ⟨3130373192456963118913265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8347661846551901650435373 3130373192456963118913265)
                      ·
                        rfl

theorem cell23_6096380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 1, 2, 1, 3].length) (baseStart_6096380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096380 prefixEnd_6096380 := by exact prefixLift 6096380
  have htrace : WordTrace (prefixWord ++ tailWord_6096380) baseStart_6096380 baseEnd_6096380 := by
    simpa [prefixWord, tailWord_6096380, baseEnd_6096380] using wordTrace_append hprefix tailTrace_6096380
  have hstable : (prefixWord ++ tailWord_6096380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096380).length < 2 ^ (prefixWord ++ tailWord_6096380).sum := by decide
  have hdescent : baseEnd_6096380 < baseStart_6096380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096397 : List Nat := [1, 7, 1, 1, 2, 1, 1, 2, 1, 3, 3]
def baseStart_6096397 : Nat := 118140960795 + 6096397 * 2 ^ 59
def prefixEnd_6096397 : Nat := 4983230072969 + 3 ^ 40 * 6096397 * 2
def baseEnd_6096397 : Nat := 3130381921628089552400687

theorem tailTrace_6096397 : CollatzResearch.WordTrace tailWord_6096397 prefixEnd_6096397 3130381921628089552400687 := by
  unfold tailWord_6096397
  simp only [CollatzResearch.WordTrace]
  refine ⟨222353865694802325559999445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148235910463201550373332963 222353865694802325559999445)
  ·
    refine ⟨5211418727221929505312487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 222353865694802325559999445 5211418727221929505312487)
    ·
      refine ⟨7817128090832894257968731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5211418727221929505312487 7817128090832894257968731)
      ·
        refine ⟨11725692136249341386953097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7817128090832894257968731 11725692136249341386953097)
        ·
          refine ⟨8794269102187006040214823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11725692136249341386953097 8794269102187006040214823)
          ·
            refine ⟨13191403653280509060322235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8794269102187006040214823 13191403653280509060322235)
            ·
              refine ⟨19787105479920763590483353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13191403653280509060322235 19787105479920763590483353)
              ·
                refine ⟨14840329109940572692862515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19787105479920763590483353 14840329109940572692862515)
                ·
                  refine ⟨22260493664910859039293773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14840329109940572692862515 22260493664910859039293773)
                  ·
                    refine ⟨8347685124341572139735165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22260493664910859039293773 8347685124341572139735165)
                    ·
                      refine ⟨3130381921628089552400687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8347685124341572139735165 3130381921628089552400687)
                      ·
                        rfl

theorem cell23_6096397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_6096397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096397 prefixEnd_6096397 := by exact prefixLift 6096397
  have htrace : WordTrace (prefixWord ++ tailWord_6096397) baseStart_6096397 baseEnd_6096397 := by
    simpa [prefixWord, tailWord_6096397, baseEnd_6096397] using wordTrace_append hprefix tailTrace_6096397
  have hstable : (prefixWord ++ tailWord_6096397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096397).length < 2 ^ (prefixWord ++ tailWord_6096397).sum := by decide
  have hdescent : baseEnd_6096397 < baseStart_6096397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096403 : List Nat := [1, 1, 1, 2, 1, 7, 1, 2, 1, 4, 2]
def baseStart_6096403 : Nat := 118140960795 + 6096403 * 2 ^ 59
def prefixEnd_6096403 : Nat := 4983230072969 + 3 ^ 40 * 6096403 * 2
def baseEnd_6096403 : Nat := 3130385002512016528925659

theorem tailTrace_6096403 : CollatzResearch.WordTrace tailWord_6096403 prefixEnd_6096403 3130385002512016528925659 := by
  unfold tailWord_6096403
  simp only [CollatzResearch.WordTrace]
  refine ⟨222354084532780588584717863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148236056355187059056478575 222354084532780588584717863)
  ·
    refine ⟨333531126799170882877076795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222354084532780588584717863 333531126799170882877076795)
    ·
      refine ⟨500296690198756324315615193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333531126799170882877076795 500296690198756324315615193)
      ·
        refine ⟨375222517649067243236711395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 500296690198756324315615193 375222517649067243236711395)
        ·
          refine ⟨562833776473600864855067093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375222517649067243236711395 562833776473600864855067093)
          ·
            refine ⟨13191416636100020270040635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 562833776473600864855067093 13191416636100020270040635)
            ·
              refine ⟨19787124954150030405060953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13191416636100020270040635 19787124954150030405060953)
              ·
                refine ⟨14840343715612522803795715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19787124954150030405060953 14840343715612522803795715)
                ·
                  refine ⟨22260515573418784205693573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14840343715612522803795715 22260515573418784205693573)
                  ·
                    refine ⟨4173846670016022038567545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22260515573418784205693573 4173846670016022038567545)
                    ·
                      refine ⟨3130385002512016528925659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4173846670016022038567545 3130385002512016528925659)
                      ·
                        rfl

theorem cell23_6096403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 4, 2].length) (baseStart_6096403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096403 prefixEnd_6096403 := by exact prefixLift 6096403
  have htrace : WordTrace (prefixWord ++ tailWord_6096403) baseStart_6096403 baseEnd_6096403 := by
    simpa [prefixWord, tailWord_6096403, baseEnd_6096403] using wordTrace_append hprefix tailTrace_6096403
  have hstable : (prefixWord ++ tailWord_6096403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096403).length < 2 ^ (prefixWord ++ tailWord_6096403).sum := by decide
  have hdescent : baseEnd_6096403 < baseStart_6096403 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096426 : List Nat := [3, 1, 4, 1, 1, 1, 2, 3, 7]
def baseStart_6096426 : Nat := 118140960795 + 6096426 * 2 ^ 59
def prefixEnd_6096426 : Nat := 4983230072969 + 3 ^ 40 * 6096426 * 2
def baseEnd_6096426 : Nat := 347821868063007770993117

theorem tailTrace_6096426 : CollatzResearch.WordTrace tailWord_6096426 prefixEnd_6096426 347821868063007770993117 := by
  unfold tailWord_6096426
  simp only [CollatzResearch.WordTrace]
  refine ⟨55588730852924315878201283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148236615607798175675203421 55588730852924315878201283)
  ·
    refine ⟨83383096279386473817301925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55588730852924315878201283 83383096279386473817301925)
    ·
      refine ⟨15634330552384963840744111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83383096279386473817301925 15634330552384963840744111)
      ·
        refine ⟨23451495828577445761116167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15634330552384963840744111 23451495828577445761116167)
        ·
          refine ⟨35177243742866168641674251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23451495828577445761116167 35177243742866168641674251)
          ·
            refine ⟨52765865614299252962511377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35177243742866168641674251 52765865614299252962511377)
            ·
              refine ⟨39574399210724439721883533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52765865614299252962511377 39574399210724439721883533)
              ·
                refine ⟨14840399704021664895706325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39574399210724439721883533 14840399704021664895706325)
                ·
                  refine ⟨347821868063007770993117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14840399704021664895706325 347821868063007770993117)
                  ·
                    rfl

theorem cell23_6096426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 7].length) (baseStart_6096426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096426 prefixEnd_6096426 := by exact prefixLift 6096426
  have htrace : WordTrace (prefixWord ++ tailWord_6096426) baseStart_6096426 baseEnd_6096426 := by
    simpa [prefixWord, tailWord_6096426, baseEnd_6096426] using wordTrace_append hprefix tailTrace_6096426
  have hstable : (prefixWord ++ tailWord_6096426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096426).length < 2 ^ (prefixWord ++ tailWord_6096426).sum := by decide
  have hdescent : baseEnd_6096426 < baseStart_6096426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096513 : List Nat := [1, 2, 4, 2, 1, 2, 2, 1, 1, 4, 3]
def baseStart_6096513 : Nat := 118140960795 + 6096513 * 2 ^ 59
def prefixEnd_6096513 : Nat := 4983230072969 + 3 ^ 40 * 6096513 * 2
def baseEnd_6096513 : Nat := 3130441485384011098550153

theorem tailTrace_6096513 : CollatzResearch.WordTrace tailWord_6096513 prefixEnd_6096513 3130441485384011098550153 := by
  unfold tailWord_6096513
  simp only [CollatzResearch.WordTrace]
  refine ⟨222358096562382077371222193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148238731041588051580814795 222358096562382077371222193)
  ·
    refine ⟨166768572421786558028416645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222358096562382077371222193 166768572421786558028416645)
    ·
      refine ⟨31269107329084979630328121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166768572421786558028416645 31269107329084979630328121)
      ·
        refine ⟨23451830496813734722746091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31269107329084979630328121 23451830496813734722746091)
        ·
          refine ⟨35177745745220602084119137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23451830496813734722746091 35177745745220602084119137)
          ·
            refine ⟨26383309308915451563089353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35177745745220602084119137 26383309308915451563089353)
            ·
              refine ⟨19787481981686588672317015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26383309308915451563089353 19787481981686588672317015)
              ·
                refine ⟨29681222972529883008475523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19787481981686588672317015 29681222972529883008475523)
                ·
                  refine ⟨44521834458794824512713285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29681222972529883008475523 44521834458794824512713285)
                  ·
                    refine ⟨8347843961024029596133741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44521834458794824512713285 8347843961024029596133741)
                    ·
                      refine ⟨3130441485384011098550153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8347843961024029596133741 3130441485384011098550153)
                      ·
                        rfl

theorem cell23_6096513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_6096513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096513 prefixEnd_6096513 := by exact prefixLift 6096513
  have htrace : WordTrace (prefixWord ++ tailWord_6096513) baseStart_6096513 baseEnd_6096513 := by
    simpa [prefixWord, tailWord_6096513, baseEnd_6096513] using wordTrace_append hprefix tailTrace_6096513
  have hstable : (prefixWord ++ tailWord_6096513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096513).length < 2 ^ (prefixWord ++ tailWord_6096513).sum := by decide
  have hdescent : baseEnd_6096513 < baseStart_6096513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096570 : List Nat := [3, 1, 1, 1, 2, 4, 1, 3, 2, 3, 2]
def baseStart_6096570 : Nat := 118140960795 + 6096570 * 2 ^ 59
def prefixEnd_6096570 : Nat := 4983230072969 + 3 ^ 40 * 6096570 * 2
def baseEnd_6096570 : Nat := 3130470753781317375537391

theorem tailTrace_6096570 : CollatzResearch.WordTrace tailWord_6096570 prefixEnd_6096570 3130470753781317375537391 := by
  unfold tailWord_6096570
  simp only [CollatzResearch.WordTrace]
  refine ⟨55590043880793894026511791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148240117015450384070698109 55590043880793894026511791)
  ·
    refine ⟨83385065821190841039767687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55590043880793894026511791 83385065821190841039767687)
    ·
      refine ⟨125077598731786261559651531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83385065821190841039767687 125077598731786261559651531)
      ·
        refine ⟨187616398097679392339477297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125077598731786261559651531 187616398097679392339477297)
        ·
          refine ⟨140712298573259544254607973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187616398097679392339477297 140712298573259544254607973)
          ·
            refine ⟨26383555982486164547738995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140712298573259544254607973 26383555982486164547738995)
            ·
              refine ⟨39575333973729246821608493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26383555982486164547738995 39575333973729246821608493)
              ·
                refine ⟨14840750240148467558103185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39575333973729246821608493 14840750240148467558103185)
                ·
                  refine ⟨11130562680111350668577389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14840750240148467558103185 11130562680111350668577389)
                  ·
                    refine ⟨4173961005041756500716521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11130562680111350668577389 4173961005041756500716521)
                    ·
                      refine ⟨3130470753781317375537391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4173961005041756500716521 3130470753781317375537391)
                      ·
                        rfl

theorem cell23_6096570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 2, 3, 2].length) (baseStart_6096570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096570 prefixEnd_6096570 := by exact prefixLift 6096570
  have htrace : WordTrace (prefixWord ++ tailWord_6096570) baseStart_6096570 baseEnd_6096570 := by
    simpa [prefixWord, tailWord_6096570, baseEnd_6096570] using wordTrace_append hprefix tailTrace_6096570
  have hstable : (prefixWord ++ tailWord_6096570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096570).length < 2 ^ (prefixWord ++ tailWord_6096570).sum := by decide
  have hdescent : baseEnd_6096570 < baseStart_6096570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096594 : List Nat := [3, 2, 2, 2, 2, 2, 1, 4, 1, 1, 3]
def baseStart_6096594 : Nat := 118140960795 + 6096594 * 2 ^ 59
def prefixEnd_6096594 : Nat := 4983230072969 + 3 ^ 40 * 6096594 * 2
def baseEnd_6096594 : Nat := 3130483077317025281637281

theorem tailTrace_6096594 : CollatzResearch.WordTrace tailWord_6096594 prefixEnd_6096594 3130483077317025281637281 := by
  unfold tailWord_6096594
  simp only [CollatzResearch.WordTrace]
  refine ⟨55590262718772157051230209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148240700583392418803280557 55590262718772157051230209)
  ·
    refine ⟨41692697039079117788422657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55590262718772157051230209 41692697039079117788422657)
    ·
      refine ⟨31269522779309338341316993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41692697039079117788422657 31269522779309338341316993)
      ·
        refine ⟨23452142084482003755987745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31269522779309338341316993 23452142084482003755987745)
        ·
          refine ⟨17589106563361502816990809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23452142084482003755987745 17589106563361502816990809)
          ·
            refine ⟨13191829922521127112743107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17589106563361502816990809 13191829922521127112743107)
            ·
              refine ⟨19787744883781690669114661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13191829922521127112743107 19787744883781690669114661)
              ·
                refine ⟨3710202165709067000458999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19787744883781690669114661 3710202165709067000458999)
                ·
                  refine ⟨5565303248563600500688499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3710202165709067000458999 5565303248563600500688499)
                  ·
                    refine ⟨8347954872845400751032749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5565303248563600500688499 8347954872845400751032749)
                    ·
                      refine ⟨3130483077317025281637281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8347954872845400751032749 3130483077317025281637281)
                      ·
                        rfl

theorem cell23_6096594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_6096594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096594 prefixEnd_6096594 := by exact prefixLift 6096594
  have htrace : WordTrace (prefixWord ++ tailWord_6096594) baseStart_6096594 baseEnd_6096594 := by
    simpa [prefixWord, tailWord_6096594, baseEnd_6096594] using wordTrace_append hprefix tailTrace_6096594
  have hstable : (prefixWord ++ tailWord_6096594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096594).length < 2 ^ (prefixWord ++ tailWord_6096594).sum := by decide
  have hdescent : baseEnd_6096594 < baseStart_6096594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096623 : List Nat := [1, 1, 2, 1, 5, 1, 5, 7]
def baseStart_6096623 : Nat := 118140960795 + 6096623 * 2 ^ 59
def prefixEnd_6096623 : Nat := 4983230072969 + 3 ^ 40 * 6096623 * 2
def baseEnd_6096623 : Nat := 115944369194666876599061

theorem tailTrace_6096623 : CollatzResearch.WordTrace tailWord_6096623 prefixEnd_6096623 115944369194666876599061 := by
  unfold tailWord_6096623
  simp only [CollatzResearch.WordTrace]
  refine ⟨222362108591983566157726523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148241405727989044105151015 222362108591983566157726523)
  ·
    refine ⟨333543162887975349236589785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222362108591983566157726523 333543162887975349236589785)
    ·
      refine ⟨250157372165981511927442339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333543162887975349236589785 250157372165981511927442339)
      ·
        refine ⟨375236058248972267891163509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250157372165981511927442339 375236058248972267891163509)
        ·
          refine ⟨35178380460841150114796579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 375236058248972267891163509 35178380460841150114796579)
          ·
            refine ⟨52767570691261725172194869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35178380460841150114796579 52767570691261725172194869)
            ·
              refine ⟨4946959752305786734893269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52767570691261725172194869 4946959752305786734893269)
              ·
                refine ⟨115944369194666876599061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4946959752305786734893269 115944369194666876599061)
                ·
                  rfl

theorem cell23_6096623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 7].length) (baseStart_6096623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096623 prefixEnd_6096623 := by exact prefixLift 6096623
  have htrace : WordTrace (prefixWord ++ tailWord_6096623) baseStart_6096623 baseEnd_6096623 := by
    simpa [prefixWord, tailWord_6096623, baseEnd_6096623] using wordTrace_append hprefix tailTrace_6096623
  have hstable : (prefixWord ++ tailWord_6096623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096623).length < 2 ^ (prefixWord ++ tailWord_6096623).sum := by decide
  have hdescent : baseEnd_6096623 < baseStart_6096623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096628 : List Nat := [2, 6, 1, 1, 1, 2, 2, 3, 1, 1, 3]
def baseStart_6096628 : Nat := 118140960795 + 6096628 * 2 ^ 59
def prefixEnd_6096628 : Nat := 4983230072969 + 3 ^ 40 * 6096628 * 2
def baseEnd_6096628 : Nat := 3130500535659278148612125

theorem tailTrace_6096628 : CollatzResearch.WordTrace tailWord_6096628 prefixEnd_6096628 3130500535659278148612125 := by
  unfold tailWord_6096628
  simp only [CollatzResearch.WordTrace]
  refine ⟨111181145478482726005829269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148241527304643634674439025 111181145478482726005829269)
  ·
    refine ⟨5211616194303877781523247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 111181145478482726005829269 5211616194303877781523247)
    ·
      refine ⟨7817424291455816672284871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5211616194303877781523247 7817424291455816672284871)
      ·
        refine ⟨11726136437183725008427307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7817424291455816672284871 11726136437183725008427307)
        ·
          refine ⟨17589204655775587512640961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11726136437183725008427307 17589204655775587512640961)
          ·
            refine ⟨13191903491831690634480721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17589204655775587512640961 13191903491831690634480721)
            ·
              refine ⟨9893927618873767975860541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13191903491831690634480721 9893927618873767975860541)
              ·
                refine ⟨3710222857077662990947703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9893927618873767975860541 3710222857077662990947703)
                ·
                  refine ⟨5565334285616494486421555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3710222857077662990947703 5565334285616494486421555)
                  ·
                    refine ⟨8348001428424741729632333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5565334285616494486421555 8348001428424741729632333)
                    ·
                      refine ⟨3130500535659278148612125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8348001428424741729632333 3130500535659278148612125)
                      ·
                        rfl

theorem cell23_6096628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_6096628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096628 prefixEnd_6096628 := by exact prefixLift 6096628
  have htrace : WordTrace (prefixWord ++ tailWord_6096628) baseStart_6096628 baseEnd_6096628 := by
    simpa [prefixWord, tailWord_6096628, baseEnd_6096628] using wordTrace_append hprefix tailTrace_6096628
  have hstable : (prefixWord ++ tailWord_6096628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096628).length < 2 ^ (prefixWord ++ tailWord_6096628).sum := by decide
  have hdescent : baseEnd_6096628 < baseStart_6096628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096630 : List Nat := [5, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4]
def baseStart_6096630 : Nat := 118140960795 + 6096630 * 2 ^ 59
def prefixEnd_6096630 : Nat := 4983230072969 + 3 ^ 40 * 6096630 * 2
def baseEnd_6096630 : Nat := 3130501562620587140787115

theorem tailTrace_6096630 : CollatzResearch.WordTrace tailWord_6096630 prefixEnd_6096630 3130501562620587140787115 := by
  unfold tailWord_6096630
  simp only [CollatzResearch.WordTrace]
  refine ⟨13897647743934887897076959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148241575935305470902154229 13897647743934887897076959)
  ·
    refine ⟨20846471615902331845615439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13897647743934887897076959 20846471615902331845615439)
    ·
      refine ⟨31269707423853497768423159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20846471615902331845615439 31269707423853497768423159)
      ·
        refine ⟨46904561135780246652634739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31269707423853497768423159 46904561135780246652634739)
        ·
          refine ⟨70356841703670369978952109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46904561135780246652634739 70356841703670369978952109)
          ·
            refine ⟨26383815638876388742107041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70356841703670369978952109 26383815638876388742107041)
            ·
              refine ⟨19787861729157291556580281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26383815638876388742107041 19787861729157291556580281)
              ·
                refine ⟨14840896296867968667435211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19787861729157291556580281 14840896296867968667435211)
                ·
                  refine ⟨22261344445301953001152817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14840896296867968667435211 22261344445301953001152817)
                  ·
                    refine ⟨16696008333976464750864613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22261344445301953001152817 16696008333976464750864613)
                    ·
                      refine ⟨3130501562620587140787115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16696008333976464750864613 3130501562620587140787115)
                      ·
                        rfl

theorem cell23_6096630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_6096630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096630 prefixEnd_6096630 := by exact prefixLift 6096630
  have htrace : WordTrace (prefixWord ++ tailWord_6096630) baseStart_6096630 baseEnd_6096630 := by
    simpa [prefixWord, tailWord_6096630, baseEnd_6096630] using wordTrace_append hprefix tailTrace_6096630
  have hstable : (prefixWord ++ tailWord_6096630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096630).length < 2 ^ (prefixWord ++ tailWord_6096630).sum := by decide
  have hdescent : baseEnd_6096630 < baseStart_6096630 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096677 : List Nat := [1, 3, 1, 2, 3, 2, 1, 4, 1, 3, 2]
def baseStart_6096677 : Nat := 118140960795 + 6096677 * 2 ^ 59
def prefixEnd_6096677 : Nat := 4983230072969 + 3 ^ 40 * 6096677 * 2
def baseEnd_6096677 : Nat := 3130525696211348456899399

theorem tailTrace_6096677 : CollatzResearch.WordTrace tailWord_6096677 prefixEnd_6096677 3130525696211348456899399 := by
  unfold tailWord_6096677
  simp only [CollatzResearch.WordTrace]
  refine ⟨222364078133787933380192285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148242718755858622253461523 222364078133787933380192285)
  ·
    refine ⟨83386529300170475017572107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222364078133787933380192285 83386529300170475017572107)
    ·
      refine ⟨125079793950255712526358161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83386529300170475017572107 125079793950255712526358161)
      ·
        refine ⟨93809845462691784394768621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125079793950255712526358161 93809845462691784394768621)
        ·
          refine ⟨35178692048509419148038233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93809845462691784394768621 35178692048509419148038233)
          ·
            refine ⟨26384019036382064361028675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35178692048509419148038233 26384019036382064361028675)
            ·
              refine ⟨39576028554573096541543013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26384019036382064361028675 39576028554573096541543013)
              ·
                refine ⟨7420505353982455601539315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39576028554573096541543013 7420505353982455601539315)
                ·
                  refine ⟨11130758030973683402308973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7420505353982455601539315 11130758030973683402308973)
                  ·
                    refine ⟨4174034261615131275865865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11130758030973683402308973 4174034261615131275865865)
                    ·
                      refine ⟨3130525696211348456899399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4174034261615131275865865 3130525696211348456899399)
                      ·
                        rfl

theorem cell23_6096677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 4, 1, 3, 2].length) (baseStart_6096677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096677 prefixEnd_6096677 := by exact prefixLift 6096677
  have htrace : WordTrace (prefixWord ++ tailWord_6096677) baseStart_6096677 baseEnd_6096677 := by
    simpa [prefixWord, tailWord_6096677, baseEnd_6096677] using wordTrace_append hprefix tailTrace_6096677
  have hstable : (prefixWord ++ tailWord_6096677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096677).length < 2 ^ (prefixWord ++ tailWord_6096677).sum := by decide
  have hdescent : baseEnd_6096677 < baseStart_6096677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096707 : List Nat := [1, 1, 1, 3, 1, 5, 2, 1, 4, 2, 2]
def baseStart_6096707 : Nat := 118140960795 + 6096707 * 2 ^ 59
def prefixEnd_6096707 : Nat := 4983230072969 + 3 ^ 40 * 6096707 * 2
def baseEnd_6096707 : Nat := 3130541100630983339524261

theorem tailTrace_6096707 : CollatzResearch.WordTrace tailWord_6096707 prefixEnd_6096707 3130541100630983339524261 := by
  unfold tailWord_6096707
  simp only [CollatzResearch.WordTrace]
  refine ⟨222365172323679248503784375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148243448215786165669189583 222365172323679248503784375)
  ·
    refine ⟨333547758485518872755676563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222365172323679248503784375 333547758485518872755676563)
    ·
      refine ⟨500321637728278309133514845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333547758485518872755676563 500321637728278309133514845)
      ·
        refine ⟨187620614148104365925068067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 500321637728278309133514845 187620614148104365925068067)
        ·
          refine ⟨281430921222156548887602101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187620614148104365925068067 281430921222156548887602101)
          ·
            refine ⟨26384148864577176458212697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 281430921222156548887602101 26384148864577176458212697)
            ·
              refine ⟨19788111648432882343659523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26384148864577176458212697 19788111648432882343659523)
              ·
                refine ⟨29682167472649323515489285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19788111648432882343659523 29682167472649323515489285)
                ·
                  refine ⟨5565406401121748159154241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29682167472649323515489285 5565406401121748159154241)
                  ·
                    refine ⟨4174054800841311119365681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5565406401121748159154241 4174054800841311119365681)
                    ·
                      refine ⟨3130541100630983339524261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4174054800841311119365681 3130541100630983339524261)
                      ·
                        rfl

theorem cell23_6096707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 4, 2, 2].length) (baseStart_6096707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096707 prefixEnd_6096707 := by exact prefixLift 6096707
  have htrace : WordTrace (prefixWord ++ tailWord_6096707) baseStart_6096707 baseEnd_6096707 := by
    simpa [prefixWord, tailWord_6096707, baseEnd_6096707] using wordTrace_append hprefix tailTrace_6096707
  have hstable : (prefixWord ++ tailWord_6096707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096707).length < 2 ^ (prefixWord ++ tailWord_6096707).sum := by decide
  have hdescent : baseEnd_6096707 < baseStart_6096707 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096753 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 3, 2, 5]
def baseStart_6096753 : Nat := 118140960795 + 6096753 * 2 ^ 59
def prefixEnd_6096753 : Nat := 4983230072969 + 3 ^ 40 * 6096753 * 2
def baseEnd_6096753 : Nat := 3130564720741090159549049

theorem tailTrace_6096753 : CollatzResearch.WordTrace tailWord_6096753 prefixEnd_6096753 3130564720741090159549049 := by
  unfold tailWord_6096753
  simp only [CollatzResearch.WordTrace]
  refine ⟨222366850081512598359958913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148244566721008398906639275 222366850081512598359958913)
  ·
    refine ⟨166775137561134448769969185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222366850081512598359958913 166775137561134448769969185)
    ·
      refine ⟨125081353170850836577476889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166775137561134448769969185 125081353170850836577476889)
      ·
        refine ⟨93811014878138127433107667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125081353170850836577476889 93811014878138127433107667)
        ·
          refine ⟨140716522317207191149661501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93811014878138127433107667 140716522317207191149661501)
          ·
            refine ⟨52768695868952696681123063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140716522317207191149661501 52768695868952696681123063)
            ·
              refine ⟨79153043803429045021684595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52768695868952696681123063 79153043803429045021684595)
              ·
                refine ⟨118729565705143567532526893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79153043803429045021684595 118729565705143567532526893)
                ·
                  refine ⟨44523587139428837824697585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118729565705143567532526893 44523587139428837824697585)
                  ·
                    refine ⟨33392690354571628368523189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44523587139428837824697585 33392690354571628368523189)
                    ·
                      refine ⟨3130564720741090159549049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33392690354571628368523189 3130564720741090159549049)
                      ·
                        rfl

theorem cell23_6096753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_6096753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096753 prefixEnd_6096753 := by exact prefixLift 6096753
  have htrace : WordTrace (prefixWord ++ tailWord_6096753) baseStart_6096753 baseEnd_6096753 := by
    simpa [prefixWord, tailWord_6096753, baseEnd_6096753] using wordTrace_append hprefix tailTrace_6096753
  have hstable : (prefixWord ++ tailWord_6096753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096753).length < 2 ^ (prefixWord ++ tailWord_6096753).sum := by decide
  have hdescent : baseEnd_6096753 < baseStart_6096753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096758 : List Nat := [5, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2]
def baseStart_6096758 : Nat := 118140960795 + 6096758 * 2 ^ 59
def prefixEnd_6096758 : Nat := 4983230072969 + 3 ^ 40 * 6096758 * 2
def baseEnd_6096758 : Nat := 3130567288144362639986527

theorem tailTrace_6096758 : CollatzResearch.WordTrace tailWord_6096758 prefixEnd_6096758 3130567288144362639986527 := by
  unfold tailWord_6096758
  simp only [CollatzResearch.WordTrace]
  refine ⟨13897939527905905263368183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148244688297662989475927285 13897939527905905263368183)
  ·
    refine ⟨20846909291858857895052275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13897939527905905263368183 20846909291858857895052275)
    ·
      refine ⟨31270363937788286842578413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20846909291858857895052275 31270363937788286842578413)
      ·
        refine ⟨11726386476670607565966905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31270363937788286842578413 11726386476670607565966905)
        ·
          refine ⟨8794789857502955674475179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11726386476670607565966905 8794789857502955674475179)
          ·
            refine ⟨13192184786254433511712769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8794789857502955674475179 13192184786254433511712769)
            ·
              refine ⟨9894138589690825133784577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13192184786254433511712769 9894138589690825133784577)
              ·
                refine ⟨7420603942268118850338433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9894138589690825133784577 7420603942268118850338433)
                ·
                  refine ⟨5565452956701089137753825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7420603942268118850338433 5565452956701089137753825)
                  ·
                    refine ⟨4174089717525816853315369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5565452956701089137753825 4174089717525816853315369)
                    ·
                      refine ⟨3130567288144362639986527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4174089717525816853315369 3130567288144362639986527)
                      ·
                        rfl

theorem cell23_6096758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_6096758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096758 prefixEnd_6096758 := by exact prefixLift 6096758
  have htrace : WordTrace (prefixWord ++ tailWord_6096758) baseStart_6096758 baseEnd_6096758 := by
    simpa [prefixWord, tailWord_6096758, baseEnd_6096758] using wordTrace_append hprefix tailTrace_6096758
  have hstable : (prefixWord ++ tailWord_6096758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096758).length < 2 ^ (prefixWord ++ tailWord_6096758).sum := by decide
  have hdescent : baseEnd_6096758 < baseStart_6096758 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096763 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 3, 3, 4]
def baseStart_6096763 : Nat := 118140960795 + 6096763 * 2 ^ 59
def prefixEnd_6096763 : Nat := 4983230072969 + 3 ^ 40 * 6096763 * 2
def baseEnd_6096763 : Nat := 3130569855547635120424003

theorem tailTrace_6096763 : CollatzResearch.WordTrace tailWord_6096763 prefixEnd_6096763 3130569855547635120424003 := by
  unfold tailWord_6096763
  simp only [CollatzResearch.WordTrace]
  refine ⟨222367214811476370067822943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148244809874317580045215295 222367214811476370067822943)
  ·
    refine ⟨333550822217214555101734415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222367214811476370067822943 333550822217214555101734415)
    ·
      refine ⟨500326233325821832652601623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333550822217214555101734415 500326233325821832652601623)
      ·
        refine ⟨750489349988732748978902435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500326233325821832652601623 750489349988732748978902435)
        ·
          refine ⟨1125734024983099123468353653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 750489349988732748978902435 1125734024983099123468353653)
          ·
            refine ⟨105537564842165542825158155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1125734024983099123468353653 105537564842165542825158155)
            ·
              refine ⟨158306347263248314237737233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105537564842165542825158155 158306347263248314237737233)
              ·
                refine ⟨118729760447436235678302925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158306347263248314237737233 118729760447436235678302925)
                ·
                  refine ⟨44523660167788588379363597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118729760447436235678302925 44523660167788588379363597)
                  ·
                    refine ⟨16696372562920720642261349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44523660167788588379363597 16696372562920720642261349)
                    ·
                      refine ⟨3130569855547635120424003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16696372562920720642261349 3130569855547635120424003)
                      ·
                        rfl

theorem cell23_6096763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 3, 4].length) (baseStart_6096763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096763 prefixEnd_6096763 := by exact prefixLift 6096763
  have htrace : WordTrace (prefixWord ++ tailWord_6096763) baseStart_6096763 baseEnd_6096763 := by
    simpa [prefixWord, tailWord_6096763, baseEnd_6096763] using wordTrace_append hprefix tailTrace_6096763
  have hstable : (prefixWord ++ tailWord_6096763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096763).length < 2 ^ (prefixWord ++ tailWord_6096763).sum := by decide
  have hdescent : baseEnd_6096763 < baseStart_6096763 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096797 : List Nat := [1, 4, 2, 1, 2, 2, 3, 1, 2, 1, 4]
def baseStart_6096797 : Nat := 118140960795 + 6096797 * 2 ^ 59
def prefixEnd_6096797 : Nat := 4983230072969 + 3 ^ 40 * 6096797 * 2
def baseEnd_6096797 : Nat := 3130587313889887987398847

theorem tailTrace_6096797 : CollatzResearch.WordTrace tailWord_6096797 prefixEnd_6096797 3130587313889887987398847 := by
  unfold tailWord_6096797
  simp only [CollatzResearch.WordTrace]
  refine ⟨222368454893353193874560645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148245636595568795916373763 222368454893353193874560645)
  ·
    refine ⟨41694085292503723851480121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222368454893353193874560645 41694085292503723851480121)
    ·
      refine ⟨31270563969377792888610091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41694085292503723851480121 31270563969377792888610091)
      ·
        refine ⟨46905845954066689332915137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31270563969377792888610091 46905845954066689332915137)
        ·
          refine ⟨35179384465550016999686353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46905845954066689332915137 35179384465550016999686353)
          ·
            refine ⟨26384538349162512749764765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35179384465550016999686353 26384538349162512749764765)
            ·
              refine ⟨9894201880935942281161787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26384538349162512749764765 9894201880935942281161787)
              ·
                refine ⟨14841302821403913421742681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9894201880935942281161787 14841302821403913421742681)
                ·
                  refine ⟨11130977116052935066307011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14841302821403913421742681 11130977116052935066307011)
                  ·
                    refine ⟨16696465674079402599460517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11130977116052935066307011 16696465674079402599460517)
                    ·
                      refine ⟨3130587313889887987398847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16696465674079402599460517 3130587313889887987398847)
                      ·
                        rfl

theorem cell23_6096797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_6096797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096797 prefixEnd_6096797 := by exact prefixLift 6096797
  have htrace : WordTrace (prefixWord ++ tailWord_6096797) baseStart_6096797 baseEnd_6096797 := by
    simpa [prefixWord, tailWord_6096797, baseEnd_6096797] using wordTrace_append hprefix tailTrace_6096797
  have hstable : (prefixWord ++ tailWord_6096797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096797).length < 2 ^ (prefixWord ++ tailWord_6096797).sum := by decide
  have hdescent : baseEnd_6096797 < baseStart_6096797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096803 : List Nat := [1, 1, 1, 4, 1, 2, 1, 4, 8]
def baseStart_6096803 : Nat := 118140960795 + 6096803 * 2 ^ 59
def prefixEnd_6096803 : Nat := 4983230072969 + 3 ^ 40 * 6096803 * 2
def baseEnd_6096803 : Nat := 347843377197090551547091

theorem tailTrace_6096803 : CollatzResearch.WordTrace tailWord_6096803 prefixEnd_6096803 347843377197090551547091 := by
  unfold tailWord_6096803
  simp only [CollatzResearch.WordTrace]
  refine ⟨222368673731331456899279063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148245782487554304599519375 222368673731331456899279063)
  ·
    refine ⟨333553010596997185348918595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222368673731331456899279063 333553010596997185348918595)
    ·
      refine ⟨500329515895495778023377893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333553010596997185348918595 500329515895495778023377893)
      ·
        refine ⟨93811784230405458379383355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 500329515895495778023377893 93811784230405458379383355)
        ·
          refine ⟨140717676345608187569075033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93811784230405458379383355 140717676345608187569075033)
          ·
            refine ⟨105538257259206140676806275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140717676345608187569075033 105538257259206140676806275)
            ·
              refine ⟨158307385888809211015209413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105538257259206140676806275 158307385888809211015209413)
              ·
                refine ⟨29682634854151727065351765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 158307385888809211015209413 29682634854151727065351765)
                ·
                  refine ⟨347843377197090551547091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29682634854151727065351765 347843377197090551547091)
                  ·
                    rfl

theorem cell23_6096803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 8].length) (baseStart_6096803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096803 prefixEnd_6096803 := by exact prefixLift 6096803
  have htrace : WordTrace (prefixWord ++ tailWord_6096803) baseStart_6096803 baseEnd_6096803 := by
    simpa [prefixWord, tailWord_6096803, baseEnd_6096803] using wordTrace_append hprefix tailTrace_6096803
  have hstable : (prefixWord ++ tailWord_6096803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096803).length < 2 ^ (prefixWord ++ tailWord_6096803).sum := by decide
  have hdescent : baseEnd_6096803 < baseStart_6096803 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096847 : List Nat := [1, 1, 2, 1, 1, 5, 1, 4, 3, 1, 3]
def baseStart_6096847 : Nat := 118140960795 + 6096847 * 2 ^ 59
def prefixEnd_6096847 : Nat := 4983230072969 + 3 ^ 40 * 6096847 * 2
def baseEnd_6096847 : Nat := 3130612987922612791773617

theorem tailTrace_6096847 : CollatzResearch.WordTrace tailWord_6096847 prefixEnd_6096847 3130612987922612791773617 := by
  unfold tailWord_6096847
  simp only [CollatzResearch.WordTrace]
  refine ⟨222370278543172052413880795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148246852362114701609253863 222370278543172052413880795)
  ·
    refine ⟨333555417814758078620821193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222370278543172052413880795 333555417814758078620821193)
    ·
      refine ⟨250166563361068558965615895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333555417814758078620821193 250166563361068558965615895)
      ·
        refine ⟨375249845041602838448423843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250166563361068558965615895 375249845041602838448423843)
        ·
          refine ⟨562874767562404257672635765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375249845041602838448423843 562874767562404257672635765)
          ·
            refine ⟨52769509458975399156809603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 562874767562404257672635765 52769509458975399156809603)
            ·
              refine ⟨79154264188463098735214405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52769509458975399156809603 79154264188463098735214405)
              ·
                refine ⟨14841424535336831012852701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79154264188463098735214405 14841424535336831012852701)
                ·
                  refine ⟨5565534200751311629819763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14841424535336831012852701 5565534200751311629819763)
                  ·
                    refine ⟨8348301301126967444729645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5565534200751311629819763 8348301301126967444729645)
                    ·
                      refine ⟨3130612987922612791773617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8348301301126967444729645 3130612987922612791773617)
                      ·
                        rfl

theorem cell23_6096847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 3, 1, 3].length) (baseStart_6096847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096847 prefixEnd_6096847 := by exact prefixLift 6096847
  have htrace : WordTrace (prefixWord ++ tailWord_6096847) baseStart_6096847 baseEnd_6096847 := by
    simpa [prefixWord, tailWord_6096847, baseEnd_6096847] using wordTrace_append hprefix tailTrace_6096847
  have hstable : (prefixWord ++ tailWord_6096847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096847).length < 2 ^ (prefixWord ++ tailWord_6096847).sum := by decide
  have hdescent : baseEnd_6096847 < baseStart_6096847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096858 : List Nat := [3, 1, 1, 2, 6, 1, 1, 3, 1, 4]
def baseStart_6096858 : Nat := 118140960795 + 6096858 * 2 ^ 59
def prefixEnd_6096858 : Nat := 4983230072969 + 3 ^ 40 * 6096858 * 2
def baseEnd_6096858 : Nat := 1043539545403270749578689

theorem tailTrace_6096858 : CollatzResearch.WordTrace tailWord_6096858 prefixEnd_6096858 1043539545403270749578689 := by
  unfold tailWord_6096858
  simp only [CollatzResearch.WordTrace]
  refine ⟨55592669936533050323132807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148247119830754800861687485 55592669936533050323132807)
  ·
    refine ⟨83389004904799575484699211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55592669936533050323132807 83389004904799575484699211)
    ·
      refine ⟨125083507357199363227048817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83389004904799575484699211 125083507357199363227048817)
      ·
        refine ⟨93812630517899522420286613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125083507357199363227048817 93812630517899522420286613)
        ·
          refine ⟨4397467055526540113450935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 93812630517899522420286613 4397467055526540113450935)
          ·
            refine ⟨6596200583289810170176403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4397467055526540113450935 6596200583289810170176403)
            ·
              refine ⟨9894300874934715255264605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6596200583289810170176403 9894300874934715255264605)
              ·
                refine ⟨3710362828100518220724227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9894300874934715255264605 3710362828100518220724227)
                ·
                  refine ⟨5565544242150777331086341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3710362828100518220724227 5565544242150777331086341)
                  ·
                    refine ⟨1043539545403270749578689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5565544242150777331086341 1043539545403270749578689)
                    ·
                      rfl

theorem cell23_6096858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 3, 1, 4].length) (baseStart_6096858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096858 prefixEnd_6096858 := by exact prefixLift 6096858
  have htrace : WordTrace (prefixWord ++ tailWord_6096858) baseStart_6096858 baseEnd_6096858 := by
    simpa [prefixWord, tailWord_6096858, baseEnd_6096858] using wordTrace_append hprefix tailTrace_6096858
  have hstable : (prefixWord ++ tailWord_6096858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096858).length < 2 ^ (prefixWord ++ tailWord_6096858).sum := by decide
  have hdescent : baseEnd_6096858 < baseStart_6096858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096867 : List Nat := [1, 1, 1, 6, 1, 2, 2, 3, 1, 5]
def baseStart_6096867 : Nat := 118140960795 + 6096867 * 2 ^ 59
def prefixEnd_6096867 : Nat := 4983230072969 + 3 ^ 40 * 6096867 * 2
def baseEnd_6096867 : Nat := 1043541085845234237841175

theorem tailTrace_6096867 : CollatzResearch.WordTrace tailWord_6096867 prefixEnd_6096867 1043541085845234237841175 := by
  unfold tailWord_6096867
  simp only [CollatzResearch.WordTrace]
  refine ⟨222371008003099595829608855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148247338668733063886405903 222371008003099595829608855)
  ·
    refine ⟨333556512004649393744413283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222371008003099595829608855 333556512004649393744413283)
    ·
      refine ⟨500334768006974090616619925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333556512004649393744413283 500334768006974090616619925)
      ·
        refine ⟨23453192250326910497654059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 500334768006974090616619925 23453192250326910497654059)
        ·
          refine ⟨35179788375490365746481089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23453192250326910497654059 35179788375490365746481089)
          ·
            refine ⟨26384841281617774309860817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35179788375490365746481089 26384841281617774309860817)
            ·
              refine ⟨19788630961213330732395613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26384841281617774309860817 19788630961213330732395613)
              ·
                refine ⟨7420736610454999024648355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19788630961213330732395613 7420736610454999024648355)
                ·
                  refine ⟨11131104915682498536972533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7420736610454999024648355 11131104915682498536972533)
                  ·
                    refine ⟨1043541085845234237841175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11131104915682498536972533 1043541085845234237841175)
                    ·
                      rfl

theorem cell23_6096867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 3, 1, 5].length) (baseStart_6096867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096867 prefixEnd_6096867 := by exact prefixLift 6096867
  have htrace : WordTrace (prefixWord ++ tailWord_6096867) baseStart_6096867 baseEnd_6096867 := by
    simpa [prefixWord, tailWord_6096867, baseEnd_6096867] using wordTrace_append hprefix tailTrace_6096867
  have hstable : (prefixWord ++ tailWord_6096867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096867).length < 2 ^ (prefixWord ++ tailWord_6096867).sum := by decide
  have hdescent : baseEnd_6096867 < baseStart_6096867 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096874 : List Nat := [3, 1, 3, 1, 2, 1, 3, 2, 2, 3, 2]
def baseStart_6096874 : Nat := 118140960795 + 6096874 * 2 ^ 59
def prefixEnd_6096874 : Nat := 4983230072969 + 3 ^ 40 * 6096874 * 2
def baseEnd_6096874 : Nat := 3130626851900284186135993

theorem tailTrace_6096874 : CollatzResearch.WordTrace tailWord_6096874 prefixEnd_6096874 3130626851900284186135993 := by
  unfold tailWord_6096874
  simp only [CollatzResearch.WordTrace]
  refine ⟨55592815828518559006278419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148247508876049490683409117 55592815828518559006278419)
  ·
    refine ⟨83389223742777838509417629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55592815828518559006278419 83389223742777838509417629)
    ·
      refine ⟨31270958903541689441031611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83389223742777838509417629 31270958903541689441031611)
      ·
        refine ⟨46906438355312534161547417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31270958903541689441031611 46906438355312534161547417)
        ·
          refine ⟨35179828766484400621160563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46906438355312534161547417 35179828766484400621160563)
          ·
            refine ⟨52769743149726600931740845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35179828766484400621160563 52769743149726600931740845)
            ·
              refine ⟨19788653681147475349402817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52769743149726600931740845 19788653681147475349402817)
              ·
                refine ⟨14841490260860606512052113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19788653681147475349402817 14841490260860606512052113)
                ·
                  refine ⟨11131117695645454884039085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14841490260860606512052113 11131117695645454884039085)
                  ·
                    refine ⟨4174169135867045581514657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11131117695645454884039085 4174169135867045581514657)
                    ·
                      refine ⟨3130626851900284186135993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4174169135867045581514657 3130626851900284186135993)
                      ·
                        rfl

theorem cell23_6096874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 2, 3, 2].length) (baseStart_6096874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096874 prefixEnd_6096874 := by exact prefixLift 6096874
  have htrace : WordTrace (prefixWord ++ tailWord_6096874) baseStart_6096874 baseEnd_6096874 := by
    simpa [prefixWord, tailWord_6096874, baseEnd_6096874] using wordTrace_append hprefix tailTrace_6096874
  have hstable : (prefixWord ++ tailWord_6096874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096874).length < 2 ^ (prefixWord ++ tailWord_6096874).sum := by decide
  have hdescent : baseEnd_6096874 < baseStart_6096874 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096881 : List Nat := [1, 2, 2, 2, 5, 2, 1, 1, 3, 1, 3]
def baseStart_6096881 : Nat := 118140960795 + 6096881 * 2 ^ 59
def prefixEnd_6096881 : Nat := 4983230072969 + 3 ^ 40 * 6096881 * 2
def baseEnd_6096881 : Nat := 3130630446264865658748461

theorem tailTrace_6096881 : CollatzResearch.WordTrace tailWord_6096881 prefixEnd_6096881 3130630446264865658748461 := by
  unfold tailWord_6096881
  simp only [CollatzResearch.WordTrace]
  refine ⟨222371518625048876220618497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148247679083365917480412331 222371518625048876220618497)
  ·
    refine ⟨166778638968786657165463873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222371518625048876220618497 166778638968786657165463873)
    ·
      refine ⟨125083979226589992874097905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166778638968786657165463873 125083979226589992874097905)
      ·
        refine ⟨93812984419942494655573429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125083979226589992874097905 93812984419942494655573429)
        ·
          refine ⟨8794967289369608873960009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93812984419942494655573429 8794967289369608873960009)
          ·
            refine ⟨6596225467027206655470007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8794967289369608873960009 6596225467027206655470007)
            ·
              refine ⟨9894338200540809983205011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6596225467027206655470007 9894338200540809983205011)
              ·
                refine ⟨14841507300811214974807517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9894338200540809983205011 14841507300811214974807517)
                ·
                  refine ⟨5565565237804205615552819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14841507300811214974807517 5565565237804205615552819)
                  ·
                    refine ⟨8348347856706308423329229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5565565237804205615552819 8348347856706308423329229)
                    ·
                      refine ⟨3130630446264865658748461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8348347856706308423329229 3130630446264865658748461)
                      ·
                        rfl

theorem cell23_6096881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 3, 1, 3].length) (baseStart_6096881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096881 prefixEnd_6096881 := by exact prefixLift 6096881
  have htrace : WordTrace (prefixWord ++ tailWord_6096881) baseStart_6096881 baseEnd_6096881 := by
    simpa [prefixWord, tailWord_6096881, baseEnd_6096881] using wordTrace_append hprefix tailTrace_6096881
  have hstable : (prefixWord ++ tailWord_6096881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096881).length < 2 ^ (prefixWord ++ tailWord_6096881).sum := by decide
  have hdescent : baseEnd_6096881 < baseStart_6096881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096890 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 1, 8, 3]
def baseStart_6096890 : Nat := 118140960795 + 6096890 * 2 ^ 59
def prefixEnd_6096890 : Nat := 4983230072969 + 3 ^ 40 * 6096890 * 2
def baseEnd_6096890 : Nat := 3130635067590756123535919

theorem tailTrace_6096890 : CollatzResearch.WordTrace tailWord_6096890 prefixEnd_6096890 3130635067590756123535919 := by
  unfold tailWord_6096890
  simp only [CollatzResearch.WordTrace]
  refine ⟨55592961720504067689424031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148247897921344180505130749 55592961720504067689424031)
  ·
    refine ⟨83389442580756101534136047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55592961720504067689424031 83389442580756101534136047)
    ·
      refine ⟨125084163871134152301204071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83389442580756101534136047 125084163871134152301204071)
      ·
        refine ⟨187626245806701228451806107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125084163871134152301204071 187626245806701228451806107)
        ·
          refine ⟨281439368710051842677709161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187626245806701228451806107 281439368710051842677709161)
          ·
            refine ⟨211079526532538882008281871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281439368710051842677709161 211079526532538882008281871)
            ·
              refine ⟨316619289798808323012422807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211079526532538882008281871 316619289798808323012422807)
              ·
                refine ⟨474928934698212484518634211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 316619289798808323012422807 474928934698212484518634211)
                ·
                  refine ⟨712393402047318726777951317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 474928934698212484518634211 712393402047318726777951317)
                  ·
                    refine ⟨8348360180242016329429117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 712393402047318726777951317 8348360180242016329429117)
                    ·
                      refine ⟨3130635067590756123535919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8348360180242016329429117 3130635067590756123535919)
                      ·
                        rfl

theorem cell23_6096890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 1, 8, 3].length) (baseStart_6096890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096890 prefixEnd_6096890 := by exact prefixLift 6096890
  have htrace : WordTrace (prefixWord ++ tailWord_6096890) baseStart_6096890 baseEnd_6096890 := by
    simpa [prefixWord, tailWord_6096890, baseEnd_6096890] using wordTrace_append hprefix tailTrace_6096890
  have hstable : (prefixWord ++ tailWord_6096890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096890).length < 2 ^ (prefixWord ++ tailWord_6096890).sum := by decide
  have hdescent : baseEnd_6096890 < baseStart_6096890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096904 : List Nat := [2, 1, 3, 2, 1, 2, 2, 1, 5, 2, 2]
def baseStart_6096904 : Nat := 118140960795 + 6096904 * 2 ^ 59
def prefixEnd_6096904 : Nat := 4983230072969 + 3 ^ 40 * 6096904 * 2
def baseEnd_6096904 : Nat := 3130642256319919068760855

theorem tailTrace_6096904 : CollatzResearch.WordTrace tailWord_6096904 prefixEnd_6096904 3130642256319919068760855 := by
  unfold tailWord_6096904
  simp only [CollatzResearch.WordTrace]
  refine ⟨111186178751982775574352883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148248238335977034099137177 111186178751982775574352883)
  ·
    refine ⟨166779268127974163361529325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111186178751982775574352883 166779268127974163361529325)
    ·
      refine ⟨62542225547990311260573497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166779268127974163361529325 62542225547990311260573497)
      ·
        refine ⟨46906669160992733445430123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62542225547990311260573497 46906669160992733445430123)
        ·
          refine ⟨70360003741489100168145185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46906669160992733445430123 70360003741489100168145185)
          ·
            refine ⟨52770002806116825126108889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70360003741489100168145185 52770002806116825126108889)
            ·
              refine ⟨39577502104587618844581667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52770002806116825126108889 39577502104587618844581667)
              ·
                refine ⟨59366253156881428266872501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39577502104587618844581667 59366253156881428266872501)
                ·
                  refine ⟨5565586233457633900019297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59366253156881428266872501 5565586233457633900019297)
                  ·
                    refine ⟨4174189675093225425014473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5565586233457633900019297 4174189675093225425014473)
                    ·
                      refine ⟨3130642256319919068760855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4174189675093225425014473 3130642256319919068760855)
                      ·
                        rfl

theorem cell23_6096904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 5, 2, 2].length) (baseStart_6096904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096904 prefixEnd_6096904 := by exact prefixLift 6096904
  have htrace : WordTrace (prefixWord ++ tailWord_6096904) baseStart_6096904 baseEnd_6096904 := by
    simpa [prefixWord, tailWord_6096904, baseEnd_6096904] using wordTrace_append hprefix tailTrace_6096904
  have hstable : (prefixWord ++ tailWord_6096904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096904).length < 2 ^ (prefixWord ++ tailWord_6096904).sum := by decide
  have hdescent : baseEnd_6096904 < baseStart_6096904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096907 : List Nat := [1, 1, 1, 1, 6, 1, 3, 1, 3, 2, 3]
def baseStart_6096907 : Nat := 118140960795 + 6096907 * 2 ^ 59
def prefixEnd_6096907 : Nat := 4983230072969 + 3 ^ 40 * 6096907 * 2
def baseEnd_6096907 : Nat := 3130643796761882557023341

theorem tailTrace_6096907 : CollatzResearch.WordTrace tailWord_6096907 prefixEnd_6096907 3130643796761882557023341 := by
  unfold tailWord_6096907
  simp only [CollatzResearch.WordTrace]
  refine ⟨222372466922954682661064975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148248311281969788440709983 222372466922954682661064975)
  ·
    refine ⟨333558700384432023991597463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222372466922954682661064975 333558700384432023991597463)
    ·
      refine ⟨500338050576648035987396195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333558700384432023991597463 500338050576648035987396195)
      ·
        refine ⟨750507075864972053981094293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500338050576648035987396195 750507075864972053981094293)
        ·
          refine ⟨35180019181170565030363795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 750507075864972053981094293 35180019181170565030363795)
          ·
            refine ⟨52770028771755847545545693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35180019181170565030363795 52770028771755847545545693)
            ·
              refine ⟨19788760789408442829579635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52770028771755847545545693 19788760789408442829579635)
              ·
                refine ⟨29683141184112664244369453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19788760789408442829579635 29683141184112664244369453)
                ·
                  refine ⟨11131177944042249091638545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29683141184112664244369453 11131177944042249091638545)
                  ·
                    refine ⟨8348383458031686818728909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11131177944042249091638545 8348383458031686818728909)
                    ·
                      refine ⟨3130643796761882557023341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8348383458031686818728909 3130643796761882557023341)
                      ·
                        rfl

theorem cell23_6096907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 3, 2, 3].length) (baseStart_6096907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096907 prefixEnd_6096907 := by exact prefixLift 6096907
  have htrace : WordTrace (prefixWord ++ tailWord_6096907) baseStart_6096907 baseEnd_6096907 := by
    simpa [prefixWord, tailWord_6096907, baseEnd_6096907] using wordTrace_append hprefix tailTrace_6096907
  have hstable : (prefixWord ++ tailWord_6096907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096907).length < 2 ^ (prefixWord ++ tailWord_6096907).sum := by decide
  have hdescent : baseEnd_6096907 < baseStart_6096907 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096910 : List Nat := [4, 1, 1, 2, 2, 1, 1, 11]
def baseStart_6096910 : Nat := 118140960795 + 6096910 * 2 ^ 59
def prefixEnd_6096910 : Nat := 4983230072969 + 3 ^ 40 * 6096910 * 2
def baseEnd_6096910 : Nat := 115949827303846149825401

theorem tailTrace_6096910 : CollatzResearch.WordTrace tailWord_6096910 prefixEnd_6096910 115949827303846149825401 := by
  unfold tailWord_6096910
  simp only [CollatzResearch.WordTrace]
  refine ⟨27796572042742976771678023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148248384227962542782282789 27796572042742976771678023)
  ·
    refine ⟨41694858064114465157517035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27796572042742976771678023 41694858064114465157517035)
    ·
      refine ⟨62542287096171697736275553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41694858064114465157517035 62542287096171697736275553)
      ·
        refine ⟨46906715322128773302206665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62542287096171697736275553 46906715322128773302206665)
        ·
          refine ⟨35180036491596579976654999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46906715322128773302206665 35180036491596579976654999)
          ·
            refine ⟨52770054737394869964982499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35180036491596579976654999 52770054737394869964982499)
            ·
              refine ⟨79155082106092304947473749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52770054737394869964982499 79155082106092304947473749)
              ·
                refine ⟨115949827303846149825401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 79155082106092304947473749 115949827303846149825401)
                ·
                  rfl

theorem cell23_6096910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 11].length) (baseStart_6096910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096910 prefixEnd_6096910 := by exact prefixLift 6096910
  have htrace : WordTrace (prefixWord ++ tailWord_6096910) baseStart_6096910 baseEnd_6096910 := by
    simpa [prefixWord, tailWord_6096910, baseEnd_6096910] using wordTrace_append hprefix tailTrace_6096910
  have hstable : (prefixWord ++ tailWord_6096910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096910).length < 2 ^ (prefixWord ++ tailWord_6096910).sum := by decide
  have hdescent : baseEnd_6096910 < baseStart_6096910 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096921 : List Nat := [1, 2, 1, 2, 1, 1, 3, 7, 1, 2, 2]
def baseStart_6096921 : Nat := 118140960795 + 6096921 * 2 ^ 59
def prefixEnd_6096921 : Nat := 4983230072969 + 3 ^ 40 * 6096921 * 2
def baseEnd_6096921 : Nat := 3130650985491045502248277

theorem tailTrace_6096921 : CollatzResearch.WordTrace tailWord_6096921 prefixEnd_6096921 3130650985491045502248277 := by
  unfold tailWord_6096921
  simp only [CollatzResearch.WordTrace]
  refine ⟨222372977544903963052074617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148248651696602642034716411 222372977544903963052074617)
  ·
    refine ⟨166779733158677972289055963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222372977544903963052074617 166779733158677972289055963)
    ·
      refine ⟨250169599738016958433583945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166779733158677972289055963 250169599738016958433583945)
      ·
        refine ⟨187627199803512718825187959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250169599738016958433583945 187627199803512718825187959)
        ·
          refine ⟨281440799705269078237781939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187627199803512718825187959 281440799705269078237781939)
          ·
            refine ⟨422161199557903617356672909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281440799705269078237781939 422161199557903617356672909)
            ·
              refine ⟨158310449834213856508752341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 422161199557903617356672909 158310449834213856508752341)
              ·
                refine ⟨3710401167989387261923883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 158310449834213856508752341 3710401167989387261923883)
                ·
                  refine ⟨5565601751984080892885825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3710401167989387261923883 5565601751984080892885825)
                  ·
                    refine ⟨4174201313988060669664369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5565601751984080892885825 4174201313988060669664369)
                    ·
                      refine ⟨3130650985491045502248277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4174201313988060669664369 3130650985491045502248277)
                      ·
                        rfl

theorem cell23_6096921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 7, 1, 2, 2].length) (baseStart_6096921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096921 prefixEnd_6096921 := by exact prefixLift 6096921
  have htrace : WordTrace (prefixWord ++ tailWord_6096921) baseStart_6096921 baseEnd_6096921 := by
    simpa [prefixWord, tailWord_6096921, baseEnd_6096921] using wordTrace_append hprefix tailTrace_6096921
  have hstable : (prefixWord ++ tailWord_6096921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096921).length < 2 ^ (prefixWord ++ tailWord_6096921).sum := by decide
  have hdescent : baseEnd_6096921 < baseStart_6096921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096924 : List Nat := [2, 2, 3, 1, 3, 3, 1, 1, 1, 1, 5]
def baseStart_6096924 : Nat := 118140960795 + 6096924 * 2 ^ 59
def prefixEnd_6096924 : Nat := 4983230072969 + 3 ^ 40 * 6096924 * 2
def baseEnd_6096924 : Nat := 3130652525933008990510763

theorem tailTrace_6096924 : CollatzResearch.WordTrace tailWord_6096924 prefixEnd_6096924 3130652525933008990510763 := by
  unfold tailWord_6096924
  simp only [CollatzResearch.WordTrace]
  refine ⟨111186543481946547282216913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148248724642595396376289217 111186543481946547282216913)
  ·
    refine ⟨83389907611459910461662685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111186543481946547282216913 83389907611459910461662685)
    ·
      refine ⟨31271215354297466423123507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83389907611459910461662685 31271215354297466423123507)
      ·
        refine ⟨46906823031446199634685261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31271215354297466423123507 46906823031446199634685261)
        ·
          refine ⟨17590058636792324863006973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46906823031446199634685261 17590058636792324863006973)
          ·
            refine ⟨6596271988797121823627615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17590058636792324863006973 6596271988797121823627615)
            ·
              refine ⟨9894407983195682735441423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6596271988797121823627615 9894407983195682735441423)
              ·
                refine ⟨14841611974793524103162135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9894407983195682735441423 14841611974793524103162135)
                ·
                  refine ⟨22262417962190286154743203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14841611974793524103162135 22262417962190286154743203)
                  ·
                    refine ⟨33393626943285429232114805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22262417962190286154743203 33393626943285429232114805)
                    ·
                      refine ⟨3130652525933008990510763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33393626943285429232114805 3130652525933008990510763)
                      ·
                        rfl

theorem cell23_6096924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_6096924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096924 prefixEnd_6096924 := by exact prefixLift 6096924
  have htrace : WordTrace (prefixWord ++ tailWord_6096924) baseStart_6096924 baseEnd_6096924 := by
    simpa [prefixWord, tailWord_6096924, baseEnd_6096924] using wordTrace_append hprefix tailTrace_6096924
  have hstable : (prefixWord ++ tailWord_6096924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096924).length < 2 ^ (prefixWord ++ tailWord_6096924).sum := by decide
  have hdescent : baseEnd_6096924 < baseStart_6096924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096932 : List Nat := [2, 3, 1, 4, 3, 1, 2, 2, 1, 1, 3]
def baseStart_6096932 : Nat := 118140960795 + 6096932 * 2 ^ 59
def prefixEnd_6096932 : Nat := 4983230072969 + 3 ^ 40 * 6096932 * 2
def baseEnd_6096932 : Nat := 3130656633778244959210727

theorem tailTrace_6096932 : CollatzResearch.WordTrace tailWord_6096932 prefixEnd_6096932 3130656633778244959210727 := by
  unfold tailWord_6096932
  simp only [CollatzResearch.WordTrace]
  refine ⟨111186689373932055965362525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148248919165242741287150033 111186689373932055965362525)
  ·
    refine ⟨41695008515224520987010947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111186689373932055965362525 41695008515224520987010947)
    ·
      refine ⟨62542512772836781480516421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41695008515224520987010947 62542512772836781480516421)
      ·
        refine ⟨11726721144906896527596829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62542512772836781480516421 11726721144906896527596829)
        ·
          refine ⟨4397520429340086197848811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11726721144906896527596829 4397520429340086197848811)
          ·
            refine ⟨6596280644010129296773217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4397520429340086197848811 6596280644010129296773217)
            ·
              refine ⟨4947210483007596972579913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6596280644010129296773217 4947210483007596972579913)
              ·
                refine ⟨3710407862255697729434935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4947210483007596972579913 3710407862255697729434935)
                ·
                  refine ⟨5565611793383546594152403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3710407862255697729434935 5565611793383546594152403)
                  ·
                    refine ⟨8348417690075319891228605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5565611793383546594152403 8348417690075319891228605)
                    ·
                      refine ⟨3130656633778244959210727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8348417690075319891228605 3130656633778244959210727)
                      ·
                        rfl

theorem cell23_6096932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_6096932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096932 prefixEnd_6096932 := by exact prefixLift 6096932
  have htrace : WordTrace (prefixWord ++ tailWord_6096932) baseStart_6096932 baseEnd_6096932 := by
    simpa [prefixWord, tailWord_6096932, baseEnd_6096932] using wordTrace_append hprefix tailTrace_6096932
  have hstable : (prefixWord ++ tailWord_6096932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096932).length < 2 ^ (prefixWord ++ tailWord_6096932).sum := by decide
  have hdescent : baseEnd_6096932 < baseStart_6096932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096937 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 10, 1, 3]
def baseStart_6096937 : Nat := 118140960795 + 6096937 * 2 ^ 59
def prefixEnd_6096937 : Nat := 4983230072969 + 3 ^ 40 * 6096937 * 2
def baseEnd_6096937 : Nat := 3130659201181517439648203

theorem tailTrace_6096937 : CollatzResearch.WordTrace tailWord_6096937 prefixEnd_6096937 3130659201181517439648203 := by
  unfold tailWord_6096937
  simp only [CollatzResearch.WordTrace]
  refine ⟨222373561112845997784657065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148249040741897331856438043 222373561112845997784657065)
  ·
    refine ⟨166780170834634498338492799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222373561112845997784657065 166780170834634498338492799)
    ·
      refine ⟨250170256251951747507739199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166780170834634498338492799 250170256251951747507739199)
      ·
        refine ⟨375255384377927621261608799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250170256251951747507739199 375255384377927621261608799)
        ·
          refine ⟨562883076566891431892413199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375255384377927621261608799 562883076566891431892413199)
          ·
            refine ⟨844324614850337147838619799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 562883076566891431892413199 844324614850337147838619799)
            ·
              refine ⟨1266486922275505721757929699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 844324614850337147838619799 1266486922275505721757929699)
              ·
                refine ⟨1899730383413258582636894549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1266486922275505721757929699 1899730383413258582636894549)
                ·
                  refine ⟨5565616357656031003819027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 1899730383413258582636894549 5565616357656031003819027)
                  ·
                    refine ⟨8348424536484046505728541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5565616357656031003819027 8348424536484046505728541)
                    ·
                      refine ⟨3130659201181517439648203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8348424536484046505728541 3130659201181517439648203)
                      ·
                        rfl

theorem cell23_6096937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 10, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 10, 1, 3].length) (baseStart_6096937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096937 prefixEnd_6096937 := by exact prefixLift 6096937
  have htrace : WordTrace (prefixWord ++ tailWord_6096937) baseStart_6096937 baseEnd_6096937 := by
    simpa [prefixWord, tailWord_6096937, baseEnd_6096937] using wordTrace_append hprefix tailTrace_6096937
  have hstable : (prefixWord ++ tailWord_6096937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096937).length < 2 ^ (prefixWord ++ tailWord_6096937).sum := by decide
  have hdescent : baseEnd_6096937 < baseStart_6096937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096970 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 3, 8]
def baseStart_6096970 : Nat := 118140960795 + 6096970 * 2 ^ 59
def prefixEnd_6096970 : Nat := 4983230072969 + 3 ^ 40 * 6096970 * 2
def baseEnd_6096970 : Nat := 1043558715347705270178517

theorem tailTrace_6096970 : CollatzResearch.WordTrace tailWord_6096970 prefixEnd_6096970 1043558715347705270178517 := by
  unfold tailWord_6096970
  simp only [CollatzResearch.WordTrace]
  refine ⟨55593691180431611105152091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148249843147817629613738909 55593691180431611105152091)
  ·
    refine ⟨83390536770647416657728137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55593691180431611105152091 83390536770647416657728137)
    ·
      refine ⟨62542902577985562493296103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83390536770647416657728137 62542902577985562493296103)
      ·
        refine ⟨93814353866978343739944155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62542902577985562493296103 93814353866978343739944155)
        ·
          refine ⟨140721530800467515609916233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93814353866978343739944155 140721530800467515609916233)
          ·
            refine ⟨105541148100350636707437175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140721530800467515609916233 105541148100350636707437175)
            ·
              refine ⟨158311722150525955061155763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105541148100350636707437175 158311722150525955061155763)
              ·
                refine ⟨237467583225788932591733645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158311722150525955061155763 237467583225788932591733645)
                ·
                  refine ⟨89050343709670849721900117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 237467583225788932591733645 89050343709670849721900117)
                  ·
                    refine ⟨1043558715347705270178517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 89050343709670849721900117 1043558715347705270178517)
                    ·
                      rfl

theorem cell23_6096970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_6096970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096970 prefixEnd_6096970 := by exact prefixLift 6096970
  have htrace : WordTrace (prefixWord ++ tailWord_6096970) baseStart_6096970 baseEnd_6096970 := by
    simpa [prefixWord, tailWord_6096970, baseEnd_6096970] using wordTrace_append hprefix tailTrace_6096970
  have hstable : (prefixWord ++ tailWord_6096970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096970).length < 2 ^ (prefixWord ++ tailWord_6096970).sum := by decide
  have hdescent : baseEnd_6096970 < baseStart_6096970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096981 : List Nat := [1, 3, 2, 2, 1, 4, 1, 3, 1, 3, 2]
def baseStart_6096981 : Nat := 118140960795 + 6096981 * 2 ^ 59
def prefixEnd_6096981 : Nat := 4983230072969 + 3 ^ 40 * 6096981 * 2
def baseEnd_6096981 : Nat := 3130681794330315267498001

theorem tailTrace_6096981 : CollatzResearch.WordTrace tailWord_6096981 prefixEnd_6096981 3130681794330315267498001 := by
  unfold tailWord_6096981
  simp only [CollatzResearch.WordTrace]
  refine ⟨222375165924686593299258797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148250110616457728866172531 222375165924686593299258797)
  ·
    refine ⟨83390687221757472487222049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222375165924686593299258797 83390687221757472487222049)
    ·
      refine ⟨62543015416318104365416537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83390687221757472487222049 62543015416318104365416537)
      ·
        refine ⟨46907261562238578274062403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62543015416318104365416537 46907261562238578274062403)
        ·
          refine ⟨70360892343357867411093605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46907261562238578274062403 70360892343357867411093605)
          ·
            refine ⟨13192667314379600139580051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70360892343357867411093605 13192667314379600139580051)
            ·
              refine ⟨19789000971569400209370077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13192667314379600139580051 19789000971569400209370077)
              ·
                refine ⟨7420875364338525078513779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19789000971569400209370077 7420875364338525078513779)
                ·
                  refine ⟨11131313046507787617770669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7420875364338525078513779 11131313046507787617770669)
                  ·
                    refine ⟨4174242392440420356664001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11131313046507787617770669 4174242392440420356664001)
                    ·
                      refine ⟨3130681794330315267498001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4174242392440420356664001 3130681794330315267498001)
                      ·
                        rfl

theorem cell23_6096981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 3, 1, 3, 2].length) (baseStart_6096981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096981 prefixEnd_6096981 := by exact prefixLift 6096981
  have htrace : WordTrace (prefixWord ++ tailWord_6096981) baseStart_6096981 baseEnd_6096981 := by
    simpa [prefixWord, tailWord_6096981, baseEnd_6096981] using wordTrace_append hprefix tailTrace_6096981
  have hstable : (prefixWord ++ tailWord_6096981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096981).length < 2 ^ (prefixWord ++ tailWord_6096981).sum := by decide
  have hdescent : baseEnd_6096981 < baseStart_6096981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6096988 : List Nat := [2, 2, 4, 1, 1, 4, 1, 2, 2, 1, 3]
def baseStart_6096988 : Nat := 118140960795 + 6096988 * 2 ^ 59
def prefixEnd_6096988 : Nat := 4983230072969 + 3 ^ 40 * 6096988 * 2
def baseEnd_6096988 : Nat := 3130685388694896740110469

theorem tailTrace_6096988 : CollatzResearch.WordTrace tailWord_6096988 prefixEnd_6096988 3130685388694896740110469 := by
  unfold tailWord_6096988
  simp only [CollatzResearch.WordTrace]
  refine ⟨111187710617830616747381809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148250280823774155663175745 111187710617830616747381809)
  ·
    refine ⟨83390782963372962560536357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111187710617830616747381809 83390782963372962560536357)
    ·
      refine ⟨15635771805632430480100567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83390782963372962560536357 15635771805632430480100567)
      ·
        refine ⟨23453657708448645720150851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15635771805632430480100567 23453657708448645720150851)
        ·
          refine ⟨35180486562672968580226277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23453657708448645720150851 35180486562672968580226277)
          ·
            refine ⟨6596341230501181608792427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35180486562672968580226277 6596341230501181608792427)
            ·
              refine ⟨9894511845751772413188641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6596341230501181608792427 9894511845751772413188641)
              ·
                refine ⟨7420883884313829309891481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9894511845751772413188641 7420883884313829309891481)
                ·
                  refine ⟨5565662913235371982418611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7420883884313829309891481 5565662913235371982418611)
                  ·
                    refine ⟨8348494369853057973627917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5565662913235371982418611 8348494369853057973627917)
                    ·
                      refine ⟨3130685388694896740110469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8348494369853057973627917 3130685388694896740110469)
                      ·
                        rfl

theorem cell23_6096988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_6096988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6096988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6096988 prefixEnd_6096988 := by exact prefixLift 6096988
  have htrace : WordTrace (prefixWord ++ tailWord_6096988) baseStart_6096988 baseEnd_6096988 := by
    simpa [prefixWord, tailWord_6096988, baseEnd_6096988] using wordTrace_append hprefix tailTrace_6096988
  have hstable : (prefixWord ++ tailWord_6096988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6096988).length < 2 ^ (prefixWord ++ tailWord_6096988).sum := by decide
  have hdescent : baseEnd_6096988 < baseStart_6096988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6096988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
