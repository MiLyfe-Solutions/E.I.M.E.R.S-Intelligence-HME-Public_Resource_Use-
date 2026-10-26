import V185TrunkScan23Chunk0075

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_450733 : List Nat := [1, 5, 2, 1, 2, 3, 1, 3, 5]
def baseStart_450733 : Nat := 118140960795 + 450733 * 2 ^ 59
def prefixEnd_450733 : Nat := 4983230072969 + 3 ^ 40 * 450733 * 2
def baseEnd_450733 : Nat := 25715852871454470973847

theorem tailTrace_450733 : CollatzResearch.WordTrace tailWord_450733 prefixEnd_450733 25715852871454470973847 := by
  unfold tailWord_450733
  simp only [CollatzResearch.WordTrace]
  refine ⟨16439583076078794912892853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10959722050719196608595235 16439583076078794912892853)
  ·
    refine ⟨1541210913382387023083705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16439583076078794912892853 1541210913382387023083705)
    ·
      refine ⟨1155908185036790267312779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1541210913382387023083705 1155908185036790267312779)
      ·
        refine ⟨1733862277555185400969169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1155908185036790267312779 1733862277555185400969169)
        ·
          refine ⟨1300396708166389050726877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1733862277555185400969169 1300396708166389050726877)
          ·
            refine ⟨487648765562395894022579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1300396708166389050726877 487648765562395894022579)
            ·
              refine ⟨731473148343593841033869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 487648765562395894022579 731473148343593841033869)
              ·
                refine ⟨274302430628847690387701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 731473148343593841033869 274302430628847690387701)
                ·
                  refine ⟨25715852871454470973847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 274302430628847690387701 25715852871454470973847)
                  ·
                    rfl

theorem cell23_450733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_450733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450733 prefixEnd_450733 := by exact prefixLift 450733
  have htrace : WordTrace (prefixWord ++ tailWord_450733) baseStart_450733 baseEnd_450733 := by
    simpa [prefixWord, tailWord_450733, baseEnd_450733] using wordTrace_append hprefix tailTrace_450733
  have hstable : (prefixWord ++ tailWord_450733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450733).length < 2 ^ (prefixWord ++ tailWord_450733).sum := by decide
  have hdescent : baseEnd_450733 < baseStart_450733 := by decide
  rcases family_descends (prefixWord ++ tailWord_450733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450810 : List Nat := [3, 1, 1, 1, 1, 7, 2, 2, 1, 4]
def baseStart_450810 : Nat := 118140960795 + 450810 * 2 ^ 59
def prefixEnd_450810 : Nat := 4983230072969 + 3 ^ 40 * 450810 * 2
def baseEnd_450810 : Nat := 77160737951162145833923

theorem tailTrace_450810 : CollatzResearch.WordTrace tailWord_450810 prefixEnd_450810 77160737951162145833923 := by
  unfold tailWord_450810
  simp only [CollatzResearch.WordTrace]
  refine ⟨4110597874199959265861471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10961594331199891375630589 4110597874199959265861471)
  ·
    refine ⟨6165896811299938898792207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4110597874199959265861471 6165896811299938898792207)
    ·
      refine ⟨9248845216949908348188311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6165896811299938898792207 9248845216949908348188311)
      ·
        refine ⟨13873267825424862522282467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9248845216949908348188311 13873267825424862522282467)
        ·
          refine ⟨20809901738137293783423701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13873267825424862522282467 20809901738137293783423701)
          ·
            refine ⟨487732071987592823048993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 20809901738137293783423701 487732071987592823048993)
            ·
              refine ⟨365799053990694617286745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 487732071987592823048993 365799053990694617286745)
              ·
                refine ⟨274349290493020962965059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 365799053990694617286745 274349290493020962965059)
                ·
                  refine ⟨411523935739531444447589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 274349290493020962965059 411523935739531444447589)
                  ·
                    refine ⟨77160737951162145833923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 411523935739531444447589 77160737951162145833923)
                    ·
                      rfl

theorem cell23_450810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 2, 1, 4].length) (baseStart_450810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450810 prefixEnd_450810 := by exact prefixLift 450810
  have htrace : WordTrace (prefixWord ++ tailWord_450810) baseStart_450810 baseEnd_450810 := by
    simpa [prefixWord, tailWord_450810, baseEnd_450810] using wordTrace_append hprefix tailTrace_450810
  have hstable : (prefixWord ++ tailWord_450810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450810).length < 2 ^ (prefixWord ++ tailWord_450810).sum := by decide
  have hdescent : baseEnd_450810 < baseStart_450810 := by decide
  rcases family_descends (prefixWord ++ tailWord_450810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450826 : List Nat := [3, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2]
def baseStart_450826 : Nat := 118140960795 + 450826 * 2 ^ 59
def prefixEnd_450826 : Nat := 4983230072969 + 3 ^ 40 * 450826 * 2
def baseEnd_450826 : Nat := 231490429543958374901695

theorem tailTrace_450826 : CollatzResearch.WordTrace tailWord_450826 prefixEnd_450826 231490429543958374901695 := by
  unfold tailWord_450826
  simp only [CollatzResearch.WordTrace]
  refine ⟨4110743766185467949007083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10961983376494581197352221 4110743766185467949007083)
  ·
    refine ⟨6166115649278201923510625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4110743766185467949007083 6166115649278201923510625)
    ·
      refine ⟨4624586736958651442632969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6166115649278201923510625 4624586736958651442632969)
      ·
        refine ⟨3468440052718988581974727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4624586736958651442632969 3468440052718988581974727)
        ·
          refine ⟨5202660079078482872962091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3468440052718988581974727 5202660079078482872962091)
          ·
            refine ⟨7803990118617724309443137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5202660079078482872962091 7803990118617724309443137)
            ·
              refine ⟨5852992588963293232082353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7803990118617724309443137 5852992588963293232082353)
              ·
                refine ⟨4389744441722469924061765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5852992588963293232082353 4389744441722469924061765)
                ·
                  refine ⟨823077082822963110761581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4389744441722469924061765 823077082822963110761581)
                  ·
                    refine ⟨308653906058611166535593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 823077082822963110761581 308653906058611166535593)
                    ·
                      refine ⟨231490429543958374901695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 308653906058611166535593 231490429543958374901695)
                      ·
                        rfl

theorem cell23_450826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2].length) (baseStart_450826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450826 prefixEnd_450826 := by exact prefixLift 450826
  have htrace : WordTrace (prefixWord ++ tailWord_450826) baseStart_450826 baseEnd_450826 := by
    simpa [prefixWord, tailWord_450826, baseEnd_450826] using wordTrace_append hprefix tailTrace_450826
  have hstable : (prefixWord ++ tailWord_450826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450826).length < 2 ^ (prefixWord ++ tailWord_450826).sum := by decide
  have hdescent : baseEnd_450826 < baseStart_450826 := by decide
  rcases family_descends (prefixWord ++ tailWord_450826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450849 : List Nat := [1, 2, 3, 2, 1, 1, 4, 2, 1, 6]
def baseStart_450849 : Nat := 118140960795 + 450849 * 2 ^ 59
def prefixEnd_450849 : Nat := 4983230072969 + 3 ^ 40 * 450849 * 2
def baseEnd_450849 : Nat := 77167413199670594971363

theorem tailTrace_450849 : CollatzResearch.WordTrace tailWord_450849 prefixEnd_450849 77167413199670594971363 := by
  unfold tailWord_450849
  simp only [CollatzResearch.WordTrace]
  refine ⟨16443813943658546724115601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10962542629105697816077067 16443813943658546724115601)
  ·
    refine ⟨12332860457743910043086701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16443813943658546724115601 12332860457743910043086701)
    ·
      refine ⟨4624822671653966266157513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12332860457743910043086701 4624822671653966266157513)
      ·
        refine ⟨3468617003740474699618135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4624822671653966266157513 3468617003740474699618135)
        ·
          refine ⟨5202925505610712049427203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3468617003740474699618135 5202925505610712049427203)
          ·
            refine ⟨7804388258416068074140805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5202925505610712049427203 7804388258416068074140805)
            ·
              refine ⟨1463322798453012763901401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7804388258416068074140805 1463322798453012763901401)
              ·
                refine ⟨1097492098839759572926051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1463322798453012763901401 1097492098839759572926051)
                ·
                  refine ⟨1646238148259639359389077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1097492098839759572926051 1646238148259639359389077)
                  ·
                    refine ⟨77167413199670594971363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1646238148259639359389077 77167413199670594971363)
                    ·
                      rfl

theorem cell23_450849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_450849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450849 prefixEnd_450849 := by exact prefixLift 450849
  have htrace : WordTrace (prefixWord ++ tailWord_450849) baseStart_450849 baseEnd_450849 := by
    simpa [prefixWord, tailWord_450849, baseEnd_450849] using wordTrace_append hprefix tailTrace_450849
  have hstable : (prefixWord ++ tailWord_450849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450849).length < 2 ^ (prefixWord ++ tailWord_450849).sum := by decide
  have hdescent : baseEnd_450849 < baseStart_450849 := by decide
  rcases family_descends (prefixWord ++ tailWord_450849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450850 : List Nat := [3, 3, 1, 1, 3, 1, 1, 5, 1, 1, 3]
def baseStart_450850 : Nat := 118140960795 + 450850 * 2 ^ 59
def prefixEnd_450850 : Nat := 4983230072969 + 3 ^ 40 * 450850 * 2
def baseEnd_450850 : Nat := 231502753079666281001585

theorem tailTrace_450850 : CollatzResearch.WordTrace tailWord_450850 prefixEnd_450850 231502753079666281001585 := by
  unfold tailWord_450850
  simp only [CollatzResearch.WordTrace]
  refine ⟨4110962604163730973725501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10962566944436615929934669 4110962604163730973725501)
  ·
    refine ⟨1541610976561399115147063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4110962604163730973725501 1541610976561399115147063)
    ·
      refine ⟨2312416464842098672720595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1541610976561399115147063 2312416464842098672720595)
      ·
        refine ⟨3468624697263148009080893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2312416464842098672720595 3468624697263148009080893)
        ·
          refine ⟨1300734261473680503405335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3468624697263148009080893 1300734261473680503405335)
          ·
            refine ⟨1951101392210520755108003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1300734261473680503405335 1951101392210520755108003)
            ·
              refine ⟨2926652088315781132662005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1951101392210520755108003 2926652088315781132662005)
              ·
                refine ⟨274373633279604481187063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2926652088315781132662005 274373633279604481187063)
                ·
                  refine ⟨411560449919406721780595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 274373633279604481187063 411560449919406721780595)
                  ·
                    refine ⟨617340674879110082670893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 411560449919406721780595 617340674879110082670893)
                    ·
                      refine ⟨231502753079666281001585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 617340674879110082670893 231502753079666281001585)
                      ·
                        rfl

theorem cell23_450850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 5, 1, 1, 3].length) (baseStart_450850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450850 prefixEnd_450850 := by exact prefixLift 450850
  have htrace : WordTrace (prefixWord ++ tailWord_450850) baseStart_450850 baseEnd_450850 := by
    simpa [prefixWord, tailWord_450850, baseEnd_450850] using wordTrace_append hprefix tailTrace_450850
  have hstable : (prefixWord ++ tailWord_450850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450850).length < 2 ^ (prefixWord ++ tailWord_450850).sum := by decide
  have hdescent : baseEnd_450850 < baseStart_450850 := by decide
  rcases family_descends (prefixWord ++ tailWord_450850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450869 : List Nat := [1, 3, 3, 1, 2, 1, 2, 2, 1, 1, 6]
def baseStart_450869 : Nat := 118140960795 + 450869 * 2 ^ 59
def prefixEnd_450869 : Nat := 4983230072969 + 3 ^ 40 * 450869 * 2
def baseEnd_450869 : Nat := 231512509212101706663997

theorem tailTrace_450869 : CollatzResearch.WordTrace tailWord_450869 prefixEnd_450869 231512509212101706663997 := by
  unfold tailWord_450869
  simp only [CollatzResearch.WordTrace]
  refine ⟨16444543403586090139843661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10963028935724060093229107 16444543403586090139843661)
  ·
    refine ⟨6166703776344783802441373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16444543403586090139843661 6166703776344783802441373)
    ·
      refine ⟨2312513916129293925915515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6166703776344783802441373 2312513916129293925915515)
      ·
        refine ⟨3468770874193940888873273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2312513916129293925915515 3468770874193940888873273)
        ·
          refine ⟨2601578155645455666654955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3468770874193940888873273 2601578155645455666654955)
          ·
            refine ⟨3902367233468183499982433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2601578155645455666654955 3902367233468183499982433)
            ·
              refine ⟨2926775425101137624986825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3902367233468183499982433 2926775425101137624986825)
              ·
                refine ⟨2195081568825853218740119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2926775425101137624986825 2195081568825853218740119)
                ·
                  refine ⟨3292622353238779828110179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2195081568825853218740119 3292622353238779828110179)
                  ·
                    refine ⟨4938933529858169742165269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3292622353238779828110179 4938933529858169742165269)
                    ·
                      refine ⟨231512509212101706663997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4938933529858169742165269 231512509212101706663997)
                      ·
                        rfl

theorem cell23_450869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_450869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450869 prefixEnd_450869 := by exact prefixLift 450869
  have htrace : WordTrace (prefixWord ++ tailWord_450869) baseStart_450869 baseEnd_450869 := by
    simpa [prefixWord, tailWord_450869, baseEnd_450869] using wordTrace_append hprefix tailTrace_450869
  have hstable : (prefixWord ++ tailWord_450869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450869).length < 2 ^ (prefixWord ++ tailWord_450869).sum := by decide
  have hdescent : baseEnd_450869 < baseStart_450869 := by decide
  rcases family_descends (prefixWord ++ tailWord_450869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450896 : List Nat := [2, 1, 1, 1, 1, 8, 2, 7]
def baseStart_450896 : Nat := 118140960795 + 450896 * 2 ^ 59
def prefixEnd_450896 : Nat := 4983230072969 + 3 ^ 40 * 450896 * 2
def baseEnd_450896 : Nat := 8575050858880485223199

theorem tailTrace_450896 : CollatzResearch.WordTrace tailWord_450896 prefixEnd_450896 8575050858880485223199 := by
  unfold tailWord_450896
  simp only [CollatzResearch.WordTrace]
  refine ⟨8222764087244136875538271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10963685449658849167384361 8222764087244136875538271)
  ·
    refine ⟨12334146130866205313307407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8222764087244136875538271 12334146130866205313307407)
    ·
      refine ⟨18501219196299307969961111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12334146130866205313307407 18501219196299307969961111)
      ·
        refine ⟨27751828794448961954941667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18501219196299307969961111 27751828794448961954941667)
        ·
          refine ⟨41627743191673442932412501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27751828794448961954941667 41627743191673442932412501)
          ·
            refine ⟨487825115527423159364209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 41627743191673442932412501 487825115527423159364209)
            ·
              refine ⟨365868836645567369523157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 487825115527423159364209 365868836645567369523157)
              ·
                refine ⟨8575050858880485223199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 365868836645567369523157 8575050858880485223199)
                ·
                  rfl

theorem cell23_450896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 7].length) (baseStart_450896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450896 prefixEnd_450896 := by exact prefixLift 450896
  have htrace : WordTrace (prefixWord ++ tailWord_450896) baseStart_450896 baseEnd_450896 := by
    simpa [prefixWord, tailWord_450896, baseEnd_450896] using wordTrace_append hprefix tailTrace_450896
  have hstable : (prefixWord ++ tailWord_450896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450896).length < 2 ^ (prefixWord ++ tailWord_450896).sum := by decide
  have hdescent : baseEnd_450896 < baseStart_450896 := by decide
  rcases family_descends (prefixWord ++ tailWord_450896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450924 : List Nat := [2, 2, 1, 1, 6, 1, 3, 2, 1, 2, 2]
def baseStart_450924 : Nat := 118140960795 + 450924 * 2 ^ 59
def prefixEnd_450924 : Nat := 4983230072969 + 3 ^ 40 * 450924 * 2
def baseEnd_450924 : Nat := 231540750648098991476245

theorem tailTrace_450924 : CollatzResearch.WordTrace tailWord_450924 prefixEnd_450924 231540750648098991476245 := by
  unfold tailWord_450924
  simp only [CollatzResearch.WordTrace]
  refine ⟨8223274709193417266547913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10964366278924556355397217 8223274709193417266547913)
  ·
    refine ⟨6167456031895062949910935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8223274709193417266547913 6167456031895062949910935)
    ·
      refine ⟨9251184047842594424866403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6167456031895062949910935 9251184047842594424866403)
      ·
        refine ⟨13876776071763891637299605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9251184047842594424866403 13876776071763891637299605)
        ·
          refine ⟨650473878363932420498419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13876776071763891637299605 650473878363932420498419)
          ·
            refine ⟨975710817545898630747629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 650473878363932420498419 975710817545898630747629)
            ·
              refine ⟨365891556579711986530361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 975710817545898630747629 365891556579711986530361)
              ·
                refine ⟨274418667434783989897771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 365891556579711986530361 274418667434783989897771)
                ·
                  refine ⟨411628001152175984846657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 274418667434783989897771 411628001152175984846657)
                  ·
                    refine ⟨308721000864131988634993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 411628001152175984846657 308721000864131988634993)
                    ·
                      refine ⟨231540750648098991476245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 308721000864131988634993 231540750648098991476245)
                      ·
                        rfl

theorem cell23_450924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 2, 1, 2, 2].length) (baseStart_450924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450924 prefixEnd_450924 := by exact prefixLift 450924
  have htrace : WordTrace (prefixWord ++ tailWord_450924) baseStart_450924 baseEnd_450924 := by
    simpa [prefixWord, tailWord_450924, baseEnd_450924] using wordTrace_append hprefix tailTrace_450924
  have hstable : (prefixWord ++ tailWord_450924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450924).length < 2 ^ (prefixWord ++ tailWord_450924).sum := by decide
  have hdescent : baseEnd_450924 < baseStart_450924 := by decide
  rcases family_descends (prefixWord ++ tailWord_450924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450929 : List Nat := [1, 2, 2, 2, 1, 2, 1, 3, 2, 3, 4]
def baseStart_450929 : Nat := 118140960795 + 450929 * 2 ^ 59
def prefixEnd_450929 : Nat := 4983230072969 + 3 ^ 40 * 450929 * 2
def baseEnd_450929 : Nat := 231543318051371471913721

theorem tailTrace_450929 : CollatzResearch.WordTrace tailWord_450929 prefixEnd_450929 231543318051371471913721 := by
  unfold tailWord_450929
  simp only [CollatzResearch.WordTrace]
  refine ⟨16446731783368720387027841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10964487855579146924685227 16446731783368720387027841)
  ·
    refine ⟨12335048837526540290270881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16446731783368720387027841 12335048837526540290270881)
    ·
      refine ⟨9251286628144905217703161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12335048837526540290270881 9251286628144905217703161)
      ·
        refine ⟨6938464971108678913277371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9251286628144905217703161 6938464971108678913277371)
        ·
          refine ⟨10407697456663018369916057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6938464971108678913277371 10407697456663018369916057)
          ·
            refine ⟨7805773092497263777437043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10407697456663018369916057 7805773092497263777437043)
            ·
              refine ⟨11708659638745895666155565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7805773092497263777437043 11708659638745895666155565)
              ·
                refine ⟨4390747364529710874808337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11708659638745895666155565 4390747364529710874808337)
                ·
                  refine ⟨3293060523397283156106253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4390747364529710874808337 3293060523397283156106253)
                  ·
                    refine ⟨1234897696273981183539845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3293060523397283156106253 1234897696273981183539845)
                    ·
                      refine ⟨231543318051371471913721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1234897696273981183539845 231543318051371471913721)
                      ·
                        rfl

theorem cell23_450929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_450929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450929 prefixEnd_450929 := by exact prefixLift 450929
  have htrace : WordTrace (prefixWord ++ tailWord_450929) baseStart_450929 baseEnd_450929 := by
    simpa [prefixWord, tailWord_450929, baseEnd_450929] using wordTrace_append hprefix tailTrace_450929
  have hstable : (prefixWord ++ tailWord_450929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450929).length < 2 ^ (prefixWord ++ tailWord_450929).sum := by decide
  have hdescent : baseEnd_450929 < baseStart_450929 := by decide
  rcases family_descends (prefixWord ++ tailWord_450929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450934 : List Nat := [5, 1, 1, 4, 1, 2, 2, 1, 2, 4]
def baseStart_450934 : Nat := 118140960795 + 450934 * 2 ^ 59
def prefixEnd_450934 : Nat := 4983230072969 + 3 ^ 40 * 450934 * 2
def baseEnd_450934 : Nat := 77181961818214650783733

theorem tailTrace_450934 : CollatzResearch.WordTrace tailWord_450934 prefixEnd_450934 77181961818214650783733 := by
  unfold tailWord_450934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1027932134271912890059991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10964609432233737493973237 1027932134271912890059991)
  ·
    refine ⟨1541898201407869335089987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1027932134271912890059991 1541898201407869335089987)
    ·
      refine ⟨2312847302111804002634981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1541898201407869335089987 2312847302111804002634981)
      ·
        refine ⟨433658869145963250494059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2312847302111804002634981 433658869145963250494059)
        ·
          refine ⟨650488303718944875741089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433658869145963250494059 650488303718944875741089)
          ·
            refine ⟨487866227789208656805817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 650488303718944875741089 487866227789208656805817)
            ·
              refine ⟨365899670841906492604363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 487866227789208656805817 365899670841906492604363)
              ·
                refine ⟨548849506262859738906545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365899670841906492604363 548849506262859738906545)
                ·
                  refine ⟨411637129697144804179909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 548849506262859738906545 411637129697144804179909)
                  ·
                    refine ⟨77181961818214650783733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 411637129697144804179909 77181961818214650783733)
                    ·
                      rfl

theorem cell23_450934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_450934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450934 prefixEnd_450934 := by exact prefixLift 450934
  have htrace : WordTrace (prefixWord ++ tailWord_450934) baseStart_450934 baseEnd_450934 := by
    simpa [prefixWord, tailWord_450934, baseEnd_450934] using wordTrace_append hprefix tailTrace_450934
  have hstable : (prefixWord ++ tailWord_450934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450934).length < 2 ^ (prefixWord ++ tailWord_450934).sum := by decide
  have hdescent : baseEnd_450934 < baseStart_450934 := by decide
  rcases family_descends (prefixWord ++ tailWord_450934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450980 : List Nat := [2, 3, 1, 2, 1, 1, 3, 4, 2, 2, 2]
def baseStart_450980 : Nat := 118140960795 + 450980 * 2 ^ 59
def prefixEnd_450980 : Nat := 4983230072969 + 3 ^ 40 * 450980 * 2
def baseEnd_450980 : Nat := 231569505564750772375987

theorem tailTrace_450980 : CollatzResearch.WordTrace tailWord_450980 prefixEnd_450980 231569505564750772375987 := by
  unfold tailWord_450980
  simp only [CollatzResearch.WordTrace]
  refine ⟨8224295953091978048567197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10965727937455970731422929 8224295953091978048567197)
  ·
    refine ⟨3084110982409491768212699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8224295953091978048567197 3084110982409491768212699)
    ·
      refine ⟨4626166473614237652319049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3084110982409491768212699 4626166473614237652319049)
      ·
        refine ⟨3469624855210678239239287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4626166473614237652319049 3469624855210678239239287)
        ·
          refine ⟨5204437282816017358858931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3469624855210678239239287 5204437282816017358858931)
          ·
            refine ⟨7806655924224026038288397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5204437282816017358858931 7806655924224026038288397)
            ·
              refine ⟨2927495971584009764358149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7806655924224026038288397 2927495971584009764358149)
              ·
                refine ⟨548905494672001830817153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2927495971584009764358149 548905494672001830817153)
                ·
                  refine ⟨411679121004001373112865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 548905494672001830817153 411679121004001373112865)
                  ·
                    refine ⟨308759340753001029834649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 411679121004001373112865 308759340753001029834649)
                    ·
                      refine ⟨231569505564750772375987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 308759340753001029834649 231569505564750772375987)
                      ·
                        rfl

theorem cell23_450980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 4, 2, 2, 2].length) (baseStart_450980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450980 prefixEnd_450980 := by exact prefixLift 450980
  have htrace : WordTrace (prefixWord ++ tailWord_450980) baseStart_450980 baseEnd_450980 := by
    simpa [prefixWord, tailWord_450980, baseEnd_450980] using wordTrace_append hprefix tailTrace_450980
  have hstable : (prefixWord ++ tailWord_450980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450980).length < 2 ^ (prefixWord ++ tailWord_450980).sum := by decide
  have hdescent : baseEnd_450980 < baseStart_450980 := by decide
  rcases family_descends (prefixWord ++ tailWord_450980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451016 : List Nat := [2, 1, 3, 1, 3, 3, 1, 1, 1, 7]
def baseStart_451016 : Nat := 118140960795 + 451016 * 2 ^ 59
def prefixEnd_451016 : Nat := 4983230072969 + 3 ^ 40 * 451016 * 2
def baseEnd_451016 : Nat := 77195996956104210508607

theorem tailTrace_451016 : CollatzResearch.WordTrace tailWord_451016 prefixEnd_451016 77195996956104210508607 := by
  unfold tailWord_451016
  simp only [CollatzResearch.WordTrace]
  refine ⟨8224952467026767122722451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10966603289369022830296601 8224952467026767122722451)
  ·
    refine ⟨12337428700540150684083677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8224952467026767122722451 12337428700540150684083677)
    ·
      refine ⟨4626535762702556506531379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12337428700540150684083677 4626535762702556506531379)
      ·
        refine ⟨6939803644053834759797069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4626535762702556506531379 6939803644053834759797069)
        ·
          refine ⟨2602426366520188034923901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6939803644053834759797069 2602426366520188034923901)
          ·
            refine ⟨975909887445070513096463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2602426366520188034923901 975909887445070513096463)
            ·
              refine ⟨1463864831167605769644695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 975909887445070513096463 1463864831167605769644695)
              ·
                refine ⟨2195797246751408654467043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1463864831167605769644695 2195797246751408654467043)
                ·
                  refine ⟨3293695870127112981700565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2195797246751408654467043 3293695870127112981700565)
                  ·
                    refine ⟨77195996956104210508607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3293695870127112981700565 77195996956104210508607)
                    ·
                      rfl

theorem cell23_451016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_451016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451016 prefixEnd_451016 := by exact prefixLift 451016
  have htrace : WordTrace (prefixWord ++ tailWord_451016) baseStart_451016 baseEnd_451016 := by
    simpa [prefixWord, tailWord_451016, baseEnd_451016] using wordTrace_append hprefix tailTrace_451016
  have hstable : (prefixWord ++ tailWord_451016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451016).length < 2 ^ (prefixWord ++ tailWord_451016).sum := by decide
  have hdescent : baseEnd_451016 < baseStart_451016 := by decide
  rcases family_descends (prefixWord ++ tailWord_451016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451020 : List Nat := [2, 2, 1, 4, 3, 1, 2, 3, 5]
def baseStart_451020 : Nat := 118140960795 + 451020 * 2 ^ 59
def prefixEnd_451020 : Nat := 4983230072969 + 3 ^ 40 * 451020 * 2
def baseEnd_451020 : Nat := 25732227198992290652867

theorem tailTrace_451020 : CollatzResearch.WordTrace tailWord_451020 prefixEnd_451020 25732227198992290652867 := by
  unfold tailWord_451020
  simp only [CollatzResearch.WordTrace]
  refine ⟨8225025413019521464295257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10966700550692695285727009 8225025413019521464295257)
  ·
    refine ⟨6168769059764641098221443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8225025413019521464295257 6168769059764641098221443)
    ·
      refine ⟨9253153589646961647332165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6168769059764641098221443 9253153589646961647332165)
      ·
        refine ⟨1734966298058805308874781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9253153589646961647332165 1734966298058805308874781)
        ·
          refine ⟨650612361772051990828043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1734966298058805308874781 650612361772051990828043)
          ·
            refine ⟨975918542658077986242065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 650612361772051990828043 975918542658077986242065)
            ·
              refine ⟨731938906993558489681549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 975918542658077986242065 731938906993558489681549)
              ·
                refine ⟨274477090122584433630581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 731938906993558489681549 274477090122584433630581)
                ·
                  refine ⟨25732227198992290652867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 274477090122584433630581 25732227198992290652867)
                  ·
                    rfl

theorem cell23_451020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 3, 5].length) (baseStart_451020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451020 prefixEnd_451020 := by exact prefixLift 451020
  have htrace : WordTrace (prefixWord ++ tailWord_451020) baseStart_451020 baseEnd_451020 := by
    simpa [prefixWord, tailWord_451020, baseEnd_451020] using wordTrace_append hprefix tailTrace_451020
  have hstable : (prefixWord ++ tailWord_451020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451020).length < 2 ^ (prefixWord ++ tailWord_451020).sum := by decide
  have hdescent : baseEnd_451020 < baseStart_451020 := by decide
  rcases family_descends (prefixWord ++ tailWord_451020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451053 : List Nat := [1, 5, 1, 3, 1, 1, 1, 2, 1, 3, 4]
def baseStart_451053 : Nat := 118140960795 + 451053 * 2 ^ 59
def prefixEnd_451053 : Nat := 4983230072969 + 3 ^ 40 * 451053 * 2
def baseEnd_451053 : Nat := 231606989652528986763151

theorem tailTrace_451053 : CollatzResearch.WordTrace tailWord_451053 prefixEnd_451053 231606989652528986763151 := by
  unfold tailWord_451053
  simp only [CollatzResearch.WordTrace]
  refine ⟨16451254434919489564541813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10967502956612993043027875 16451254434919489564541813)
  ·
    refine ⟨1542305103273702146675795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16451254434919489564541813 1542305103273702146675795)
    ·
      refine ⟨2313457654910553220013693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1542305103273702146675795 2313457654910553220013693)
      ·
        refine ⟨867546620591457457505135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2313457654910553220013693 867546620591457457505135)
        ·
          refine ⟨1301319930887186186257703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 867546620591457457505135 1301319930887186186257703)
          ·
            refine ⟨1951979896330779279386555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1301319930887186186257703 1951979896330779279386555)
            ·
              refine ⟨2927969844496168919079833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1951979896330779279386555 2927969844496168919079833)
              ·
                refine ⟨2195977383372126689309875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2927969844496168919079833 2195977383372126689309875)
                ·
                  refine ⟨3293966075058190033964813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2195977383372126689309875 3293966075058190033964813)
                  ·
                    refine ⟨1235237278146821262736805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3293966075058190033964813 1235237278146821262736805)
                    ·
                      refine ⟨231606989652528986763151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1235237278146821262736805 231606989652528986763151)
                      ·
                        rfl

theorem cell23_451053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_451053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451053 prefixEnd_451053 := by exact prefixLift 451053
  have htrace : WordTrace (prefixWord ++ tailWord_451053) baseStart_451053 baseEnd_451053 := by
    simpa [prefixWord, tailWord_451053, baseEnd_451053] using wordTrace_append hprefix tailTrace_451053
  have hstable : (prefixWord ++ tailWord_451053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451053).length < 2 ^ (prefixWord ++ tailWord_451053).sum := by decide
  have hdescent : baseEnd_451053 < baseStart_451053 := by decide
  rcases family_descends (prefixWord ++ tailWord_451053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451056 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 3]
def baseStart_451056 : Nat := 118140960795 + 451056 * 2 ^ 59
def prefixEnd_451056 : Nat := 4983230072969 + 3 ^ 40 * 451056 * 2
def baseEnd_451056 : Nat := 231608530094492475025637

theorem tailTrace_451056 : CollatzResearch.WordTrace tailWord_451056 prefixEnd_451056 231608530094492475025637 := by
  unfold tailWord_451056
  simp only [CollatzResearch.WordTrace]
  refine ⟨8225681926954310538450511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10967575902605747384600681 8225681926954310538450511)
  ·
    refine ⟨12338522890431465807675767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8225681926954310538450511 12338522890431465807675767)
    ·
      refine ⟨18507784335647198711513651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12338522890431465807675767 18507784335647198711513651)
      ·
        refine ⟨27761676503470798067270477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18507784335647198711513651 27761676503470798067270477)
        ·
          refine ⟨10410628688801549275226429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27761676503470798067270477 10410628688801549275226429)
          ·
            refine ⟨3903985758300580978209911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10410628688801549275226429 3903985758300580978209911)
            ·
              refine ⟨5855978637450871467314867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3903985758300580978209911 5855978637450871467314867)
              ·
                refine ⟨8783967956176307200972301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5855978637450871467314867 8783967956176307200972301)
                ·
                  refine ⟨3293987983566115200364613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8783967956176307200972301 3293987983566115200364613)
                  ·
                    refine ⟨617622746918646600068365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3293987983566115200364613 617622746918646600068365)
                    ·
                      refine ⟨231608530094492475025637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 617622746918646600068365 231608530094492475025637)
                      ·
                        rfl

theorem cell23_451056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 3].length) (baseStart_451056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451056 prefixEnd_451056 := by exact prefixLift 451056
  have htrace : WordTrace (prefixWord ++ tailWord_451056) baseStart_451056 baseEnd_451056 := by
    simpa [prefixWord, tailWord_451056, baseEnd_451056] using wordTrace_append hprefix tailTrace_451056
  have hstable : (prefixWord ++ tailWord_451056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451056).length < 2 ^ (prefixWord ++ tailWord_451056).sum := by decide
  have hdescent : baseEnd_451056 < baseStart_451056 := by decide
  rcases family_descends (prefixWord ++ tailWord_451056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451073 : List Nat := [1, 2, 4, 1, 3, 1, 2, 1, 1, 4, 3]
def baseStart_451073 : Nat := 118140960795 + 451073 * 2 ^ 59
def prefixEnd_451073 : Nat := 4983230072969 + 3 ^ 40 * 451073 * 2
def baseEnd_451073 : Nat := 231617259265618908513059

theorem tailTrace_451073 : CollatzResearch.WordTrace tailWord_451073 prefixEnd_451073 231617259265618908513059 := by
  unfold tailWord_451073
  simp only [CollatzResearch.WordTrace]
  refine ⟨16451983894847032980269873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10967989263231355320179915 16451983894847032980269873)
  ·
    refine ⟨12338987921135274735202405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16451983894847032980269873 12338987921135274735202405)
    ·
      refine ⟨2313560235212864012850451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12338987921135274735202405 2313560235212864012850451)
      ·
        refine ⟨3470340352819296019275677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2313560235212864012850451 3470340352819296019275677)
        ·
          refine ⟨1301377632307236007228379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3470340352819296019275677 1301377632307236007228379)
          ·
            refine ⟨1952066448460854010842569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1301377632307236007228379 1952066448460854010842569)
            ·
              refine ⟨1464049836345640508131927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1952066448460854010842569 1464049836345640508131927)
              ·
                refine ⟨2196074754518460762197891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1464049836345640508131927 2196074754518460762197891)
                ·
                  refine ⟨3294112131777691143296837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2196074754518460762197891 3294112131777691143296837)
                  ·
                    refine ⟨617646024708317089368157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3294112131777691143296837 617646024708317089368157)
                    ·
                      refine ⟨231617259265618908513059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 617646024708317089368157 231617259265618908513059)
                      ·
                        rfl

theorem cell23_451073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_451073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451073 prefixEnd_451073 := by exact prefixLift 451073
  have htrace : WordTrace (prefixWord ++ tailWord_451073) baseStart_451073 baseEnd_451073 := by
    simpa [prefixWord, tailWord_451073, baseEnd_451073] using wordTrace_append hprefix tailTrace_451073
  have hstable : (prefixWord ++ tailWord_451073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451073).length < 2 ^ (prefixWord ++ tailWord_451073).sum := by decide
  have hdescent : baseEnd_451073 < baseStart_451073 := by decide
  rcases family_descends (prefixWord ++ tailWord_451073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451106 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 2, 9]
def baseStart_451106 : Nat := 118140960795 + 451106 * 2 ^ 59
def prefixEnd_451106 : Nat := 4983230072969 + 3 ^ 40 * 451106 * 2
def baseEnd_451106 : Nat := 77211401375739093133469

theorem tailTrace_451106 : CollatzResearch.WordTrace tailWord_451106 prefixEnd_451106 77211401375739093133469 := by
  unfold tailWord_451106
  simp only [CollatzResearch.WordTrace]
  refine ⟨4113296875931869904055293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10968791669151653077480781 4113296875931869904055293)
  ·
    refine ⟨1542486328474451214020735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4113296875931869904055293 1542486328474451214020735)
    ·
      refine ⟨2313729492711676821031103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1542486328474451214020735 2313729492711676821031103)
      ·
        refine ⟨3470594239067515231546655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2313729492711676821031103 3470594239067515231546655)
        ·
          refine ⟨5205891358601272847319983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3470594239067515231546655 5205891358601272847319983)
          ·
            refine ⟨7808837037901909270979975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5205891358601272847319983 7808837037901909270979975)
            ·
              refine ⟨11713255556852863906469963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7808837037901909270979975 11713255556852863906469963)
              ·
                refine ⟨17569883335279295859704945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11713255556852863906469963 17569883335279295859704945)
                ·
                  refine ⟨13177412501459471894778709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17569883335279295859704945 13177412501459471894778709)
                  ·
                    refine ⟨77211401375739093133469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 13177412501459471894778709 77211401375739093133469)
                    ·
                      rfl

theorem cell23_451106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_451106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451106 prefixEnd_451106 := by exact prefixLift 451106
  have htrace : WordTrace (prefixWord ++ tailWord_451106) baseStart_451106 baseEnd_451106 := by
    simpa [prefixWord, tailWord_451106, baseEnd_451106] using wordTrace_append hprefix tailTrace_451106
  have hstable : (prefixWord ++ tailWord_451106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451106).length < 2 ^ (prefixWord ++ tailWord_451106).sum := by decide
  have hdescent : baseEnd_451106 < baseStart_451106 := by decide
  rcases family_descends (prefixWord ++ tailWord_451106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451124 : List Nat := [2, 5, 1, 3, 1, 1, 2, 1, 2, 2, 3]
def baseStart_451124 : Nat := 118140960795 + 451124 * 2 ^ 59
def prefixEnd_451124 : Nat := 4983230072969 + 3 ^ 40 * 451124 * 2
def baseEnd_451124 : Nat := 231643446778998208975325

theorem tailTrace_451124 : CollatzResearch.WordTrace tailWord_451124 prefixEnd_451124 231643446778998208975325 := by
  unfold tailWord_451124
  simp only [CollatzResearch.WordTrace]
  refine ⟨8226922008831134345188213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10969229345108179126917617 8226922008831134345188213)
  ·
    refine ⟨771273938327918844861395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8226922008831134345188213 771273938327918844861395)
    ·
      refine ⟨1156910907491878267292093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 771273938327918844861395 1156910907491878267292093)
      ·
        refine ⟨433841590309454350234535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1156910907491878267292093 433841590309454350234535)
        ·
          refine ⟨650762385464181525351803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433841590309454350234535 650762385464181525351803)
          ·
            refine ⟨976143578196272288027705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 650762385464181525351803 976143578196272288027705)
            ·
              refine ⟨732107683647204216020779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 976143578196272288027705 732107683647204216020779)
              ·
                refine ⟨1098161525470806324031169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 732107683647204216020779 1098161525470806324031169)
                ·
                  refine ⟨823621144103104743023377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1098161525470806324031169 823621144103104743023377)
                  ·
                    refine ⟨617715858077328557267533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 823621144103104743023377 617715858077328557267533)
                    ·
                      refine ⟨231643446778998208975325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 617715858077328557267533 231643446778998208975325)
                      ·
                        rfl

theorem cell23_451124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_451124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451124 prefixEnd_451124 := by exact prefixLift 451124
  have htrace : WordTrace (prefixWord ++ tailWord_451124) baseStart_451124 baseEnd_451124 := by
    simpa [prefixWord, tailWord_451124, baseEnd_451124] using wordTrace_append hprefix tailTrace_451124
  have hstable : (prefixWord ++ tailWord_451124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451124).length < 2 ^ (prefixWord ++ tailWord_451124).sum := by decide
  have hdescent : baseEnd_451124 < baseStart_451124 := by decide
  rcases family_descends (prefixWord ++ tailWord_451124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451130 : List Nat := [3, 1, 1, 1, 3, 3, 1, 3, 2, 3, 2]
def baseStart_451130 : Nat := 118140960795 + 451130 * 2 ^ 59
def prefixEnd_451130 : Nat := 4983230072969 + 3 ^ 40 * 451130 * 2
def baseEnd_451130 : Nat := 231646527662925185500297

theorem tailTrace_451130 : CollatzResearch.WordTrace tailWord_451130 prefixEnd_451130 231646527662925185500297 := by
  unfold tailWord_451130
  simp only [CollatzResearch.WordTrace]
  refine ⟨4113515713910132928773711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10969375237093687810063229 4113515713910132928773711)
  ·
    refine ⟨6170273570865199393160567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4113515713910132928773711 6170273570865199393160567)
    ·
      refine ⟨9255410356297799089740851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6170273570865199393160567 9255410356297799089740851)
      ·
        refine ⟨13883115534446698634611277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9255410356297799089740851 13883115534446698634611277)
        ·
          refine ⟨5206168325417511987979229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13883115534446698634611277 5206168325417511987979229)
          ·
            refine ⟨1952313122031566995492211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5206168325417511987979229 1952313122031566995492211)
            ·
              refine ⟨2928469683047350493238317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1952313122031566995492211 2928469683047350493238317)
              ·
                refine ⟨1098176131142756434964369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2928469683047350493238317 1098176131142756434964369)
                ·
                  refine ⟨823632098357067326223277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1098176131142756434964369 823632098357067326223277)
                  ·
                    refine ⟨308862036883900247333729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 823632098357067326223277 308862036883900247333729)
                    ·
                      refine ⟨231646527662925185500297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 308862036883900247333729 231646527662925185500297)
                      ·
                        rfl

theorem cell23_451130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 2, 3, 2].length) (baseStart_451130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451130 prefixEnd_451130 := by exact prefixLift 451130
  have htrace : WordTrace (prefixWord ++ tailWord_451130) baseStart_451130 baseEnd_451130 := by
    simpa [prefixWord, tailWord_451130, baseEnd_451130] using wordTrace_append hprefix tailTrace_451130
  have hstable : (prefixWord ++ tailWord_451130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451130).length < 2 ^ (prefixWord ++ tailWord_451130).sum := by decide
  have hdescent : baseEnd_451130 < baseStart_451130 := by decide
  rcases family_descends (prefixWord ++ tailWord_451130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451136 : List Nat := [2, 1, 1, 2, 2, 2, 3, 1, 3, 6]
def baseStart_451136 : Nat := 118140960795 + 451136 * 2 ^ 59
def prefixEnd_451136 : Nat := 4983230072969 + 3 ^ 40 * 451136 * 2
def baseEnd_451136 : Nat := 77216536182284054008423

theorem tailTrace_451136 : CollatzResearch.WordTrace tailWord_451136 prefixEnd_451136 77216536182284054008423 := by
  unfold tailWord_451136
  simp only [CollatzResearch.WordTrace]
  refine ⟨8227140846809397369906631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10969521129079196493208841 8227140846809397369906631)
  ·
    refine ⟨12340711270214096054859947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8227140846809397369906631 12340711270214096054859947)
    ·
      refine ⟨18511066905321144082289921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12340711270214096054859947 18511066905321144082289921)
      ·
        refine ⟨13883300178990858061717441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18511066905321144082289921 13883300178990858061717441)
        ·
          refine ⟨10412475134243143546288081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13883300178990858061717441 10412475134243143546288081)
          ·
            refine ⟨7809356350682357659716061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10412475134243143546288081 7809356350682357659716061)
            ·
              refine ⟨2928508631505884122393523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7809356350682357659716061 2928508631505884122393523)
              ·
                refine ⟨4392762947258826183590285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2928508631505884122393523 4392762947258826183590285)
                ·
                  refine ⟨1647286105222059818846357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4392762947258826183590285 1647286105222059818846357)
                  ·
                    refine ⟨77216536182284054008423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1647286105222059818846357 77216536182284054008423)
                    ·
                      rfl

theorem cell23_451136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 3, 6].length) (baseStart_451136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451136 prefixEnd_451136 := by exact prefixLift 451136
  have htrace : WordTrace (prefixWord ++ tailWord_451136) baseStart_451136 baseEnd_451136 := by
    simpa [prefixWord, tailWord_451136, baseEnd_451136] using wordTrace_append hprefix tailTrace_451136
  have hstable : (prefixWord ++ tailWord_451136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451136).length < 2 ^ (prefixWord ++ tailWord_451136).sum := by decide
  have hdescent : baseEnd_451136 < baseStart_451136 := by decide
  rcases family_descends (prefixWord ++ tailWord_451136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451197 : List Nat := [1, 4, 1, 1, 5, 1, 1, 3, 1, 2, 3]
def baseStart_451197 : Nat := 118140960795 + 451197 * 2 ^ 59
def prefixEnd_451197 : Nat := 4983230072969 + 3 ^ 40 * 451197 * 2
def baseEnd_451197 : Nat := 231680930866776423362489

theorem tailTrace_451197 : CollatzResearch.WordTrace tailWord_451197 prefixEnd_451197 231680930866776423362489 := by
  unfold tailWord_451197
  simp only [CollatzResearch.WordTrace]
  refine ⟨16456506546397802157783845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10971004364265201438522563 16456506546397802157783845)
  ·
    refine ⟨3085594977449587904584471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16456506546397802157783845 3085594977449587904584471)
    ·
      refine ⟨4628392466174381856876707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3085594977449587904584471 4628392466174381856876707)
      ·
        refine ⟨6942588699261572785315061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4628392466174381856876707 6942588699261572785315061)
        ·
          refine ⟨650867690555772448623287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6942588699261572785315061 650867690555772448623287)
          ·
            refine ⟨976301535833658672934931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 650867690555772448623287 976301535833658672934931)
            ·
              refine ⟨1464452303750488009402397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 976301535833658672934931 1464452303750488009402397)
              ·
                refine ⟨549169613906433003525899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1464452303750488009402397 549169613906433003525899)
                ·
                  refine ⟨823754420859649505288849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 549169613906433003525899 823754420859649505288849)
                  ·
                    refine ⟨617815815644737128966637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 823754420859649505288849 617815815644737128966637)
                    ·
                      refine ⟨231680930866776423362489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 617815815644737128966637 231680930866776423362489)
                      ·
                        rfl

theorem cell23_451197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 3, 1, 2, 3].length) (baseStart_451197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451197 prefixEnd_451197 := by exact prefixLift 451197
  have htrace : WordTrace (prefixWord ++ tailWord_451197) baseStart_451197 baseEnd_451197 := by
    simpa [prefixWord, tailWord_451197, baseEnd_451197] using wordTrace_append hprefix tailTrace_451197
  have hstable : (prefixWord ++ tailWord_451197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451197).length < 2 ^ (prefixWord ++ tailWord_451197).sum := by decide
  have hdescent : baseEnd_451197 < baseStart_451197 := by decide
  rcases family_descends (prefixWord ++ tailWord_451197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451250 : List Nat := [3, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2]
def baseStart_451250 : Nat := 118140960795 + 451250 * 2 ^ 59
def prefixEnd_451250 : Nat := 4983230072969 + 3 ^ 40 * 451250 * 2
def baseEnd_451250 : Nat := 231708145341464715999745

theorem tailTrace_451250 : CollatzResearch.WordTrace tailWord_451250 prefixEnd_451250 231708145341464715999745 := by
  unfold tailWord_451250
  simp only [CollatzResearch.WordTrace]
  refine ⟨4114609903801448052365801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10972293076803861472975469 4114609903801448052365801)
  ·
    refine ⟨3085957427851086039274351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4114609903801448052365801 3085957427851086039274351)
    ·
      refine ⟨4628936141776629058911527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3085957427851086039274351 4628936141776629058911527)
      ·
        refine ⟨6943404212664943588367291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4628936141776629058911527 6943404212664943588367291)
        ·
          refine ⟨10415106318997415382550937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6943404212664943588367291 10415106318997415382550937)
          ·
            refine ⟨7811329739248061536913203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10415106318997415382550937 7811329739248061536913203)
            ·
              refine ⟨11716994608872092305369805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7811329739248061536913203 11716994608872092305369805)
              ·
                refine ⟨4393872978327034614513677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11716994608872092305369805 4393872978327034614513677)
                ·
                  refine ⟨1647702366872637980442629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4393872978327034614513677 1647702366872637980442629)
                  ·
                    refine ⟨308944193788619621332993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1647702366872637980442629 308944193788619621332993)
                    ·
                      refine ⟨231708145341464715999745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 308944193788619621332993 231708145341464715999745)
                      ·
                        rfl

theorem cell23_451250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2].length) (baseStart_451250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451250 prefixEnd_451250 := by exact prefixLift 451250
  have htrace : WordTrace (prefixWord ++ tailWord_451250) baseStart_451250 baseEnd_451250 := by
    simpa [prefixWord, tailWord_451250, baseEnd_451250] using wordTrace_append hprefix tailTrace_451250
  have hstable : (prefixWord ++ tailWord_451250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451250).length < 2 ^ (prefixWord ++ tailWord_451250).sum := by decide
  have hdescent : baseEnd_451250 < baseStart_451250 := by decide
  rcases family_descends (prefixWord ++ tailWord_451250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451313 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 3, 2, 5]
def baseStart_451313 : Nat := 118140960795 + 451313 * 2 ^ 59
def prefixEnd_451313 : Nat := 4983230072969 + 3 ^ 40 * 451313 * 2
def baseEnd_451313 : Nat := 231740494622697969511955

theorem tailTrace_451313 : CollatzResearch.WordTrace tailWord_451313 prefixEnd_451313 231740494622697969511955 := by
  unfold tailWord_451313
  simp only [CollatzResearch.WordTrace]
  refine ⟨16460737413977553969006593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10973824942651702646004395 16460737413977553969006593)
  ·
    refine ⟨12345553060483165476754945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16460737413977553969006593 12345553060483165476754945)
    ·
      refine ⟨9259164795362374107566209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12345553060483165476754945 9259164795362374107566209)
      ·
        refine ⟨6944373596521780580674657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9259164795362374107566209 6944373596521780580674657)
        ·
          refine ⟨5208280197391335435505993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6944373596521780580674657 5208280197391335435505993)
          ·
            refine ⟨3906210148043501576629495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5208280197391335435505993 3906210148043501576629495)
            ·
              refine ⟨5859315222065252364944243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3906210148043501576629495 5859315222065252364944243)
              ·
                refine ⟨8788972833097878547416365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5859315222065252364944243 8788972833097878547416365)
                ·
                  refine ⟨3295864812411704455281137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8788972833097878547416365 3295864812411704455281137)
                  ·
                    refine ⟨2471898609308778341460853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3295864812411704455281137 2471898609308778341460853)
                    ·
                      refine ⟨231740494622697969511955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2471898609308778341460853 231740494622697969511955)
                      ·
                        rfl

theorem cell23_451313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_451313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451313 prefixEnd_451313 := by exact prefixLift 451313
  have htrace : WordTrace (prefixWord ++ tailWord_451313) baseStart_451313 baseEnd_451313 := by
    simpa [prefixWord, tailWord_451313, baseEnd_451313] using wordTrace_append hprefix tailTrace_451313
  have hstable : (prefixWord ++ tailWord_451313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451313).length < 2 ^ (prefixWord ++ tailWord_451313).sum := by decide
  have hdescent : baseEnd_451313 < baseStart_451313 := by decide
  rcases family_descends (prefixWord ++ tailWord_451313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451324 : List Nat := [2, 2, 2, 1, 3, 4, 2, 2, 5]
def baseStart_451324 : Nat := 118140960795 + 451324 * 2 ^ 59
def prefixEnd_451324 : Nat := 4983230072969 + 3 ^ 40 * 451324 * 2
def baseEnd_451324 : Nat := 25749571434433047386045

theorem tailTrace_451324 : CollatzResearch.WordTrace tailWord_451324 prefixEnd_451324 25749571434433047386045 := by
  unfold tailWord_451324
  simp only [CollatzResearch.WordTrace]
  refine ⟨8230569308468851423828513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10974092411291801898438017 8230569308468851423828513)
  ·
    refine ⟨6172926981351638567871385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8230569308468851423828513 6172926981351638567871385)
    ·
      refine ⟨4629695236013728925903539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6172926981351638567871385 4629695236013728925903539)
      ·
        refine ⟨6944542854020593388855309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4629695236013728925903539 6944542854020593388855309)
        ·
          refine ⟨2604203570257722520820741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6944542854020593388855309 2604203570257722520820741)
          ·
            refine ⟨488288169423322972653889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2604203570257722520820741 488288169423322972653889)
            ·
              refine ⟨366216127067492229490417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 488288169423322972653889 366216127067492229490417)
              ·
                refine ⟨274662095300619172117813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 366216127067492229490417 274662095300619172117813)
                ·
                  refine ⟨25749571434433047386045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 274662095300619172117813 25749571434433047386045)
                  ·
                    rfl

theorem cell23_451324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 2, 5].length) (baseStart_451324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451324 prefixEnd_451324 := by exact prefixLift 451324
  have htrace : WordTrace (prefixWord ++ tailWord_451324) baseStart_451324 baseEnd_451324 := by
    simpa [prefixWord, tailWord_451324, baseEnd_451324] using wordTrace_append hprefix tailTrace_451324
  have hstable : (prefixWord ++ tailWord_451324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451324).length < 2 ^ (prefixWord ++ tailWord_451324).sum := by decide
  have hdescent : baseEnd_451324 < baseStart_451324 := by decide
  rcases family_descends (prefixWord ++ tailWord_451324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451353 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 1, 6, 4]
def baseStart_451353 : Nat := 118140960795 + 451353 * 2 ^ 59
def prefixEnd_451353 : Nat := 4983230072969 + 3 ^ 40 * 451353 * 2
def baseEnd_451353 : Nat := 231761033848877813011771

theorem tailTrace_451353 : CollatzResearch.WordTrace tailWord_451353 prefixEnd_451353 231761033848877813011771 := by
  unfold tailWord_451353
  simp only [CollatzResearch.WordTrace]
  refine ⟨16462196333832640800462713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10974797555888427200308475 16462196333832640800462713)
  ·
    refine ⟨12346647250374480600347035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16462196333832640800462713 12346647250374480600347035)
    ·
      refine ⟨18519970875561720900520553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12346647250374480600347035 18519970875561720900520553)
      ·
        refine ⟨13889978156671290675390415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18519970875561720900520553 13889978156671290675390415)
        ·
          refine ⟨20834967235006936013085623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13889978156671290675390415 20834967235006936013085623)
          ·
            refine ⟨31252450852510404019628435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20834967235006936013085623 31252450852510404019628435)
            ·
              refine ⟨46878676278765606029442653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31252450852510404019628435 46878676278765606029442653)
              ·
                refine ⟨17579503604537102261040995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46878676278765606029442653 17579503604537102261040995)
                ·
                  refine ⟨26369255406805653391561493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17579503604537102261040995 26369255406805653391561493)
                  ·
                    refine ⟨1236058847194015002729445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26369255406805653391561493 1236058847194015002729445)
                    ·
                      refine ⟨231761033848877813011771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1236058847194015002729445 231761033848877813011771)
                      ·
                        rfl

theorem cell23_451353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 6, 4].length) (baseStart_451353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451353 prefixEnd_451353 := by exact prefixLift 451353
  have htrace : WordTrace (prefixWord ++ tailWord_451353) baseStart_451353 baseEnd_451353 := by
    simpa [prefixWord, tailWord_451353, baseEnd_451353] using wordTrace_append hprefix tailTrace_451353
  have hstable : (prefixWord ++ tailWord_451353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451353).length < 2 ^ (prefixWord ++ tailWord_451353).sum := by decide
  have hdescent : baseEnd_451353 < baseStart_451353 := by decide
  rcases family_descends (prefixWord ++ tailWord_451353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451363 : List Nat := [1, 1, 1, 4, 2, 1, 1, 4, 8]
def baseStart_451363 : Nat := 118140960795 + 451363 * 2 ^ 59
def prefixEnd_451363 : Nat := 4983230072969 + 3 ^ 40 * 451363 * 2
def baseEnd_451363 : Nat := 25751796517269197098525

theorem tailTrace_451363 : CollatzResearch.WordTrace tailWord_451363 prefixEnd_451363 25751796517269197098525 := by
  unfold tailWord_451363
  simp only [CollatzResearch.WordTrace]
  refine ⟨16462561063796412508326743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10975040709197608338884495 16462561063796412508326743)
  ·
    refine ⟨24693841595694618762490115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16462561063796412508326743 24693841595694618762490115)
    ·
      refine ⟨37040762393541928143735173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24693841595694618762490115 37040762393541928143735173)
      ·
        refine ⟨6945142948789111526950345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37040762393541928143735173 6945142948789111526950345)
        ·
          refine ⟨5208857211591833645212759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6945142948789111526950345 5208857211591833645212759)
          ·
            refine ⟨7813285817387750467819139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5208857211591833645212759 7813285817387750467819139)
            ·
              refine ⟨11719928726081625701728709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7813285817387750467819139 11719928726081625701728709)
              ·
                refine ⟨2197486636140304819074133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11719928726081625701728709 2197486636140304819074133)
                ·
                  refine ⟨25751796517269197098525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2197486636140304819074133 25751796517269197098525)
                  ·
                    rfl

theorem cell23_451363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 8].length) (baseStart_451363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451363 prefixEnd_451363 := by exact prefixLift 451363
  have htrace : WordTrace (prefixWord ++ tailWord_451363) baseStart_451363 baseEnd_451363 := by
    simpa [prefixWord, tailWord_451363, baseEnd_451363] using wordTrace_append hprefix tailTrace_451363
  have hstable : (prefixWord ++ tailWord_451363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451363).length < 2 ^ (prefixWord ++ tailWord_451363).sum := by decide
  have hdescent : baseEnd_451363 < baseStart_451363 := by decide
  rcases family_descends (prefixWord ++ tailWord_451363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451374 : List Nat := [4, 1, 3, 2, 1, 1, 1, 2, 2, 4, 2]
def baseStart_451374 : Nat := 118140960795 + 451374 * 2 ^ 59
def prefixEnd_451374 : Nat := 4983230072969 + 3 ^ 40 * 451374 * 2
def baseEnd_451374 : Nat := 231771816942622230849175

theorem tailTrace_451374 : CollatzResearch.WordTrace tailWord_451374 prefixEnd_451374 231771816942622230849175 := by
  unfold tailWord_451374
  simp only [CollatzResearch.WordTrace]
  refine ⟨2057870283344570173372147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10975308177837707591318117 2057870283344570173372147)
  ·
    refine ⟨3086805425016855260058221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2057870283344570173372147 3086805425016855260058221)
    ·
      refine ⟨1157552034381320722521833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3086805425016855260058221 1157552034381320722521833)
      ·
        refine ⟨868164025785990541891375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1157552034381320722521833 868164025785990541891375)
        ·
          refine ⟨1302246038678985812837063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 868164025785990541891375 1302246038678985812837063)
          ·
            refine ⟨1953369058018478719255595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1302246038678985812837063 1953369058018478719255595)
            ·
              refine ⟨2930053587027718078883393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1953369058018478719255595 2930053587027718078883393)
              ·
                refine ⟨2197540190270788559162545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2930053587027718078883393 2197540190270788559162545)
                ·
                  refine ⟨1648155142703091419371909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2197540190270788559162545 1648155142703091419371909)
                  ·
                    refine ⟨309029089256829641132233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1648155142703091419371909 309029089256829641132233)
                    ·
                      refine ⟨231771816942622230849175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 309029089256829641132233 231771816942622230849175)
                      ·
                        rfl

theorem cell23_451374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_451374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451374 prefixEnd_451374 := by exact prefixLift 451374
  have htrace : WordTrace (prefixWord ++ tailWord_451374) baseStart_451374 baseEnd_451374 := by
    simpa [prefixWord, tailWord_451374, baseEnd_451374] using wordTrace_append hprefix tailTrace_451374
  have hstable : (prefixWord ++ tailWord_451374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451374).length < 2 ^ (prefixWord ++ tailWord_451374).sum := by decide
  have hdescent : baseEnd_451374 < baseStart_451374 := by decide
  rcases family_descends (prefixWord ++ tailWord_451374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451383 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 8]
def baseStart_451383 : Nat := 118140960795 + 451383 * 2 ^ 59
def prefixEnd_451383 : Nat := 4983230072969 + 3 ^ 40 * 451383 * 2
def baseEnd_451383 : Nat := 231776438268512695636633

theorem tailTrace_451383 : CollatzResearch.WordTrace tailWord_451383 prefixEnd_451383 231776438268512695636633 := by
  unfold tailWord_451383
  simp only [CollatzResearch.WordTrace]
  refine ⟨16463290523723955924054803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10975527015815970616036535 16463290523723955924054803)
  ·
    refine ⟨24694935785585933886082205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16463290523723955924054803 24694935785585933886082205)
    ·
      refine ⟨9260600919594725207280827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24694935785585933886082205 9260600919594725207280827)
      ·
        refine ⟨13890901379392087810921241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9260600919594725207280827 13890901379392087810921241)
        ·
          refine ⟨10418176034544065858190931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13890901379392087810921241 10418176034544065858190931)
          ·
            refine ⟨15627264051816098787286397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10418176034544065858190931 15627264051816098787286397)
            ·
              refine ⟨5860224019431037045232399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15627264051816098787286397 5860224019431037045232399)
              ·
                refine ⟨8790336029146555567848599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5860224019431037045232399 8790336029146555567848599)
                ·
                  refine ⟨13185504043719833351772899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8790336029146555567848599 13185504043719833351772899)
                  ·
                    refine ⟨19778256065579750027659349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13185504043719833351772899 19778256065579750027659349)
                    ·
                      refine ⟨231776438268512695636633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 19778256065579750027659349 231776438268512695636633)
                      ·
                        rfl

theorem cell23_451383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_451383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451383 prefixEnd_451383 := by exact prefixLift 451383
  have htrace : WordTrace (prefixWord ++ tailWord_451383) baseStart_451383 baseEnd_451383 := by
    simpa [prefixWord, tailWord_451383, baseEnd_451383] using wordTrace_append hprefix tailTrace_451383
  have hstable : (prefixWord ++ tailWord_451383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451383).length < 2 ^ (prefixWord ++ tailWord_451383).sum := by decide
  have hdescent : baseEnd_451383 < baseStart_451383 := by decide
  rcases family_descends (prefixWord ++ tailWord_451383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451417 : List Nat := [1, 2, 1, 2, 2, 4, 2, 1, 1, 5, 2]
def baseStart_451417 : Nat := 118140960795 + 451417 * 2 ^ 59
def prefixEnd_451417 : Nat := 4983230072969 + 3 ^ 40 * 451417 * 2
def baseEnd_451417 : Nat := 231793896610765562611477

theorem tailTrace_451417 : CollatzResearch.WordTrace tailWord_451417 prefixEnd_451417 231793896610765562611477 := by
  unfold tailWord_451417
  simp only [CollatzResearch.WordTrace]
  refine ⟨16464530605600779730792505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10976353737067186487195003 16464530605600779730792505)
  ·
    refine ⟨12348397954200584798094379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16464530605600779730792505 12348397954200584798094379)
    ·
      refine ⟨18522596931300877197141569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12348397954200584798094379 18522596931300877197141569)
      ·
        refine ⟨13891947698475657897856177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18522596931300877197141569 13891947698475657897856177)
        ·
          refine ⟨10418960773856743423392133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13891947698475657897856177 10418960773856743423392133)
          ·
            refine ⟨1953555145098139391886025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10418960773856743423392133 1953555145098139391886025)
            ·
              refine ⟨1465166358823604543914519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1953555145098139391886025 1465166358823604543914519)
              ·
                refine ⟨2197749538235406815871779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1465166358823604543914519 2197749538235406815871779)
                ·
                  refine ⟨3296624307353110223807669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2197749538235406815871779 3296624307353110223807669)
                  ·
                    refine ⟨309058528814354083481969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3296624307353110223807669 309058528814354083481969)
                    ·
                      refine ⟨231793896610765562611477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 309058528814354083481969 231793896610765562611477)
                      ·
                        rfl

theorem cell23_451417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 5, 2].length) (baseStart_451417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451417 prefixEnd_451417 := by exact prefixLift 451417
  have htrace : WordTrace (prefixWord ++ tailWord_451417) baseStart_451417 baseEnd_451417 := by
    simpa [prefixWord, tailWord_451417, baseEnd_451417] using wordTrace_append hprefix tailTrace_451417
  have hstable : (prefixWord ++ tailWord_451417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451417).length < 2 ^ (prefixWord ++ tailWord_451417).sum := by decide
  have hdescent : baseEnd_451417 < baseStart_451417 := by decide
  rcases family_descends (prefixWord ++ tailWord_451417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451427 : List Nat := [1, 1, 1, 5, 3, 1, 2, 3, 1, 5]
def baseStart_451427 : Nat := 118140960795 + 451427 * 2 ^ 59
def prefixEnd_451427 : Nat := 4983230072969 + 3 ^ 40 * 451427 * 2
def baseEnd_451427 : Nat := 77266343805770174495477

theorem tailTrace_451427 : CollatzResearch.WordTrace tailWord_451427 prefixEnd_451427 77266343805770174495477 := by
  unfold tailWord_451427
  simp only [CollatzResearch.WordTrace]
  refine ⟨16464895335564551438656535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10976596890376367625771023 16464895335564551438656535)
  ·
    refine ⟨24697343003346827157984803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16464895335564551438656535 24697343003346827157984803)
    ·
      refine ⟨37046014505020240736977205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24697343003346827157984803 37046014505020240736977205)
      ·
        refine ⟨3473063859845647569091613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37046014505020240736977205 3473063859845647569091613)
        ·
          refine ⟨1302398947442117838409355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3473063859845647569091613 1302398947442117838409355)
          ·
            refine ⟨1953598421163176757614033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1302398947442117838409355 1953598421163176757614033)
            ·
              refine ⟨1465198815872382568210525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1953598421163176757614033 1465198815872382568210525)
              ·
                refine ⟨549449555952143463078947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1465198815872382568210525 549449555952143463078947)
                ·
                  refine ⟨824174333928215194618421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 549449555952143463078947 824174333928215194618421)
                  ·
                    refine ⟨77266343805770174495477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 824174333928215194618421 77266343805770174495477)
                    ·
                      rfl

theorem cell23_451427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 3, 1, 5].length) (baseStart_451427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451427 prefixEnd_451427 := by exact prefixLift 451427
  have htrace : WordTrace (prefixWord ++ tailWord_451427) baseStart_451427 baseEnd_451427 := by
    simpa [prefixWord, tailWord_451427, baseEnd_451427] using wordTrace_append hprefix tailTrace_451427
  have hstable : (prefixWord ++ tailWord_451427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451427).length < 2 ^ (prefixWord ++ tailWord_451427).sum := by decide
  have hdescent : baseEnd_451427 < baseStart_451427 := by decide
  rcases family_descends (prefixWord ++ tailWord_451427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451450 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 2, 6, 3]
def baseStart_451450 : Nat := 118140960795 + 451450 * 2 ^ 59
def prefixEnd_451450 : Nat := 4983230072969 + 3 ^ 40 * 451450 * 2
def baseEnd_451450 : Nat := 231810841472363933498825

theorem tailTrace_451450 : CollatzResearch.WordTrace tailWord_451450 prefixEnd_451450 231810841472363933498825 := by
  unfold tailWord_451450
  simp only [CollatzResearch.WordTrace]
  refine ⟨4116433553620306591685951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10977156142987484244495869 4116433553620306591685951)
  ·
    refine ⟨6174650330430459887528927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4116433553620306591685951 6174650330430459887528927)
    ·
      refine ⟨9261975495645689831293391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6174650330430459887528927 9261975495645689831293391)
      ·
        refine ⟨13892963243468534746940087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9261975495645689831293391 13892963243468534746940087)
        ·
          refine ⟨20839444865202802120410131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13892963243468534746940087 20839444865202802120410131)
          ·
            refine ⟨31259167297804203180615197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20839444865202802120410131 31259167297804203180615197)
            ·
              refine ⟨11722187736676576192730699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31259167297804203180615197 11722187736676576192730699)
              ·
                refine ⟨17583281605014864289096049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11722187736676576192730699 17583281605014864289096049)
                ·
                  refine ⟨13187461203761148216822037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17583281605014864289096049 13187461203761148216822037)
                  ·
                    refine ⟨618162243926303822663533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13187461203761148216822037 618162243926303822663533)
                    ·
                      refine ⟨231810841472363933498825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 618162243926303822663533 231810841472363933498825)
                      ·
                        rfl

theorem cell23_451450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 2, 6, 3].length) (baseStart_451450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451450 prefixEnd_451450 := by exact prefixLift 451450
  have htrace : WordTrace (prefixWord ++ tailWord_451450) baseStart_451450 baseEnd_451450 := by
    simpa [prefixWord, tailWord_451450, baseEnd_451450] using wordTrace_append hprefix tailTrace_451450
  have hstable : (prefixWord ++ tailWord_451450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451450).length < 2 ^ (prefixWord ++ tailWord_451450).sum := by decide
  have hdescent : baseEnd_451450 < baseStart_451450 := by decide
  rcases family_descends (prefixWord ++ tailWord_451450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451464 : List Nat := [2, 1, 3, 3, 2, 1, 3, 2, 1, 1, 4]
def baseStart_451464 : Nat := 118140960795 + 451464 * 2 ^ 59
def prefixEnd_451464 : Nat := 4983230072969 + 3 ^ 40 * 451464 * 2
def baseEnd_451464 : Nat := 231818030201526878723761

theorem tailTrace_451464 : CollatzResearch.WordTrace tailWord_451464 prefixEnd_451464 231818030201526878723761 := by
  unfold tailWord_451464
  simp only [CollatzResearch.WordTrace]
  refine ⟨8233122418215253378876723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10977496557620337838502297 8233122418215253378876723)
  ·
    refine ⟨12349683627322880068315085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8233122418215253378876723 12349683627322880068315085)
    ·
      refine ⟨4631131360246080025618157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12349683627322880068315085 4631131360246080025618157)
      ·
        refine ⟨1736674260092280009606809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4631131360246080025618157 1736674260092280009606809)
        ·
          refine ⟨1302505695069210007205107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1736674260092280009606809 1302505695069210007205107)
          ·
            refine ⟨1953758542603815010807661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1302505695069210007205107 1953758542603815010807661)
            ·
              refine ⟨732659453476430629052873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1953758542603815010807661 732659453476430629052873)
              ·
                refine ⟨549494590107322971789655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 732659453476430629052873 549494590107322971789655)
                ·
                  refine ⟨824241885160984457684483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 549494590107322971789655 824241885160984457684483)
                  ·
                    refine ⟨1236362827741476686526725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 824241885160984457684483 1236362827741476686526725)
                    ·
                      refine ⟨231818030201526878723761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1236362827741476686526725 231818030201526878723761)
                      ·
                        rfl

theorem cell23_451464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_451464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451464 prefixEnd_451464 := by exact prefixLift 451464
  have htrace : WordTrace (prefixWord ++ tailWord_451464) baseStart_451464 baseEnd_451464 := by
    simpa [prefixWord, tailWord_451464, baseEnd_451464] using wordTrace_append hprefix tailTrace_451464
  have hstable : (prefixWord ++ tailWord_451464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451464).length < 2 ^ (prefixWord ++ tailWord_451464).sum := by decide
  have hdescent : baseEnd_451464 < baseStart_451464 := by decide
  rcases family_descends (prefixWord ++ tailWord_451464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451474 : List Nat := [3, 2, 3, 2, 2, 1, 1, 2, 1, 6]
def baseStart_451474 : Nat := 118140960795 + 451474 * 2 ^ 59
def prefixEnd_451474 : Nat := 4983230072969 + 3 ^ 40 * 451474 * 2
def baseEnd_451474 : Nat := 77274388336023946532905

theorem tailTrace_451474 : CollatzResearch.WordTrace tailWord_451474 prefixEnd_451474 77274388336023946532905 := by
  unfold tailWord_451474
  simp only [CollatzResearch.WordTrace]
  refine ⟨4116652391598569616404369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10977739710929518977078317 4116652391598569616404369)
  ·
    refine ⟨3087489293698927212303277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4116652391598569616404369 3087489293698927212303277)
    ·
      refine ⟨1157808485137097704613729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3087489293698927212303277 1157808485137097704613729)
      ·
        refine ⟨868356363852823278460297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1157808485137097704613729 868356363852823278460297)
        ·
          refine ⟨651267272889617458845223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 868356363852823278460297 651267272889617458845223)
          ·
            refine ⟨976900909334426188267835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 651267272889617458845223 976900909334426188267835)
            ·
              refine ⟨1465351364001639282401753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 976900909334426188267835 1465351364001639282401753)
              ·
                refine ⟨1099013523001229461801315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1465351364001639282401753 1099013523001229461801315)
                ·
                  refine ⟨1648520284501844192701973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1099013523001229461801315 1648520284501844192701973)
                  ·
                    refine ⟨77274388336023946532905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1648520284501844192701973 77274388336023946532905)
                    ·
                      rfl

theorem cell23_451474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_451474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451474 prefixEnd_451474 := by exact prefixLift 451474
  have htrace : WordTrace (prefixWord ++ tailWord_451474) baseStart_451474 baseEnd_451474 := by
    simpa [prefixWord, tailWord_451474, baseEnd_451474] using wordTrace_append hprefix tailTrace_451474
  have hstable : (prefixWord ++ tailWord_451474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451474).length < 2 ^ (prefixWord ++ tailWord_451474).sum := by decide
  have hdescent : baseEnd_451474 < baseStart_451474 := by decide
  rcases family_descends (prefixWord ++ tailWord_451474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451477 : List Nat := [1, 3, 2, 1, 1, 5, 1, 2, 1, 2, 4]
def baseStart_451477 : Nat := 118140960795 + 451477 * 2 ^ 59
def prefixEnd_451477 : Nat := 4983230072969 + 3 ^ 40 * 451477 * 2
def baseEnd_451477 : Nat := 231824705450035327861201

theorem tailTrace_451477 : CollatzResearch.WordTrace tailWord_451477 prefixEnd_451477 231824705450035327861201 := by
  unfold tailWord_451477
  simp only [CollatzResearch.WordTrace]
  refine ⟨16466718985383409977976685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10977812656922273318651123 16466718985383409977976685)
  ·
    refine ⟨6175019619518778741741257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16466718985383409977976685 6175019619518778741741257)
    ·
      refine ⟨4631264714639084056305943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6175019619518778741741257 4631264714639084056305943)
      ·
        refine ⟨6946897071958626084458915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4631264714639084056305943 6946897071958626084458915)
        ·
          refine ⟨10420345607937939126688373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6946897071958626084458915 10420345607937939126688373)
          ·
            refine ⟨976907400744181793127035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10420345607937939126688373 976907400744181793127035)
            ·
              refine ⟨1465361101116272689690553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 976907400744181793127035 1465361101116272689690553)
              ·
                refine ⟨1099020825837204517267915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1465361101116272689690553 1099020825837204517267915)
                ·
                  refine ⟨1648531238755806775901873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1099020825837204517267915 1648531238755806775901873)
                  ·
                    refine ⟨1236398429066855081926405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1648531238755806775901873 1236398429066855081926405)
                    ·
                      refine ⟨231824705450035327861201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1236398429066855081926405 231824705450035327861201)
                      ·
                        rfl

theorem cell23_451477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_451477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451477 prefixEnd_451477 := by exact prefixLift 451477
  have htrace : WordTrace (prefixWord ++ tailWord_451477) baseStart_451477 baseEnd_451477 := by
    simpa [prefixWord, tailWord_451477, baseEnd_451477] using wordTrace_append hprefix tailTrace_451477
  have hstable : (prefixWord ++ tailWord_451477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451477).length < 2 ^ (prefixWord ++ tailWord_451477).sum := by decide
  have hdescent : baseEnd_451477 < baseStart_451477 := by decide
  rcases family_descends (prefixWord ++ tailWord_451477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451481 : List Nat := [1, 2, 1, 2, 1, 3, 1, 7, 1, 2, 2]
def baseStart_451481 : Nat := 118140960795 + 451481 * 2 ^ 59
def prefixEnd_451481 : Nat := 4983230072969 + 3 ^ 40 * 451481 * 2
def baseEnd_451481 : Nat := 231826759372653312211183

theorem tailTrace_451481 : CollatzResearch.WordTrace tailWord_451481 prefixEnd_451481 231826759372653312211183 := by
  unfold tailWord_451481
  simp only [CollatzResearch.WordTrace]
  refine ⟨16466864877368918661122297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10977909918245945774081531 16466864877368918661122297)
  ·
    refine ⟨12350148658026688995841723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16466864877368918661122297 12350148658026688995841723)
    ·
      refine ⟨18525222987040033493762585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12350148658026688995841723 18525222987040033493762585)
      ·
        refine ⟨13893917240280025120321939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18525222987040033493762585 13893917240280025120321939)
        ·
          refine ⟨20840875860420037680482909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13893917240280025120321939 20840875860420037680482909)
          ·
            refine ⟨7815328447657514130181091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20840875860420037680482909 7815328447657514130181091)
            ·
              refine ⟨11722992671486271195271637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7815328447657514130181091 11722992671486271195271637)
              ·
                refine ⟨274757640737959481139179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 11722992671486271195271637 274757640737959481139179)
                ·
                  refine ⟨412136461106939221708769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 274757640737959481139179 412136461106939221708769)
                  ·
                    refine ⟨309102345830204416281577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 412136461106939221708769 309102345830204416281577)
                    ·
                      refine ⟨231826759372653312211183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 309102345830204416281577 231826759372653312211183)
                      ·
                        rfl

theorem cell23_451481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 7, 1, 2, 2].length) (baseStart_451481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451481 prefixEnd_451481 := by exact prefixLift 451481
  have htrace : WordTrace (prefixWord ++ tailWord_451481) baseStart_451481 baseEnd_451481 := by
    simpa [prefixWord, tailWord_451481, baseEnd_451481] using wordTrace_append hprefix tailTrace_451481
  have hstable : (prefixWord ++ tailWord_451481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451481).length < 2 ^ (prefixWord ++ tailWord_451481).sum := by decide
  have hdescent : baseEnd_451481 < baseStart_451481 := by decide
  rcases family_descends (prefixWord ++ tailWord_451481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451514 : List Nat := [3, 1, 1, 1, 2, 1, 3, 5, 2, 1, 3]
def baseStart_451514 : Nat := 118140960795 + 451514 * 2 ^ 59
def prefixEnd_451514 : Nat := 4983230072969 + 3 ^ 40 * 451514 * 2
def baseEnd_451514 : Nat := 231843704234251683098531

theorem tailTrace_451514 : CollatzResearch.WordTrace tailWord_451514 prefixEnd_451514 231843704234251683098531 := by
  unfold tailWord_451514
  simp only [CollatzResearch.WordTrace]
  refine ⟨4117017121562341324268399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10978712324166243531382397 4117017121562341324268399)
  ·
    refine ⟨6175525682343511986402599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4117017121562341324268399 6175525682343511986402599)
    ·
      refine ⟨9263288523515267979603899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6175525682343511986402599 9263288523515267979603899)
      ·
        refine ⟨13894932785272901969405849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9263288523515267979603899 13894932785272901969405849)
        ·
          refine ⟨10421199588954676477054387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13894932785272901969405849 10421199588954676477054387)
          ·
            refine ⟨15631799383432014715581581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10421199588954676477054387 15631799383432014715581581)
            ·
              refine ⟨5861924768787005518343093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15631799383432014715581581 5861924768787005518343093)
              ·
                refine ⟨549555447073781767344665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5861924768787005518343093 549555447073781767344665)
                ·
                  refine ⟨412166585305336325508499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 549555447073781767344665 412166585305336325508499)
                  ·
                    refine ⟨618249877958004488262749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 412166585305336325508499 618249877958004488262749)
                    ·
                      refine ⟨231843704234251683098531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 618249877958004488262749 231843704234251683098531)
                      ·
                        rfl

theorem cell23_451514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 5, 2, 1, 3].length) (baseStart_451514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451514 prefixEnd_451514 := by exact prefixLift 451514
  have htrace : WordTrace (prefixWord ++ tailWord_451514) baseStart_451514 baseEnd_451514 := by
    simpa [prefixWord, tailWord_451514, baseEnd_451514] using wordTrace_append hprefix tailTrace_451514
  have hstable : (prefixWord ++ tailWord_451514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451514).length < 2 ^ (prefixWord ++ tailWord_451514).sum := by decide
  have hdescent : baseEnd_451514 < baseStart_451514 := by decide
  rcases family_descends (prefixWord ++ tailWord_451514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451530 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 3, 8]
def baseStart_451530 : Nat := 118140960795 + 451530 * 2 ^ 59
def prefixEnd_451530 : Nat := 4983230072969 + 3 ^ 40 * 451530 * 2
def baseEnd_451530 : Nat := 77283973308241206832819

theorem tailTrace_451530 : CollatzResearch.WordTrace tailWord_451530 prefixEnd_451530 77283973308241206832819 := by
  unfold tailWord_451530
  simp only [CollatzResearch.WordTrace]
  refine ⟨4117163013547850007414011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10979101369460933353104029 4117163013547850007414011)
  ·
    refine ⟨6175744520321775011121017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4117163013547850007414011 6175744520321775011121017)
    ·
      refine ⟨4631808390241331258340763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6175744520321775011121017 4631808390241331258340763)
      ·
        refine ⟨6947712585361996887511145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4631808390241331258340763 6947712585361996887511145)
        ·
          refine ⟨5210784439021497665633359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6947712585361996887511145 5210784439021497665633359)
          ·
            refine ⟨7816176658532246498450039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5210784439021497665633359 7816176658532246498450039)
            ·
              refine ⟨11724264987798369747675059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7816176658532246498450039 11724264987798369747675059)
              ·
                refine ⟨17586397481697554621512589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11724264987798369747675059 17586397481697554621512589)
                ·
                  refine ⟨6594899055636582983067221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17586397481697554621512589 6594899055636582983067221)
                  ·
                    refine ⟨77283973308241206832819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 6594899055636582983067221 77283973308241206832819)
                    ·
                      rfl

theorem cell23_451530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_451530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451530 prefixEnd_451530 := by exact prefixLift 451530
  have htrace : WordTrace (prefixWord ++ tailWord_451530) baseStart_451530 baseEnd_451530 := by
    simpa [prefixWord, tailWord_451530, baseEnd_451530] using wordTrace_append hprefix tailTrace_451530
  have hstable : (prefixWord ++ tailWord_451530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451530).length < 2 ^ (prefixWord ++ tailWord_451530).sum := by decide
  have hdescent : baseEnd_451530 < baseStart_451530 := by decide
  rcases family_descends (prefixWord ++ tailWord_451530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451567 : List Nat := [1, 1, 2, 1, 4, 3, 2, 1, 2, 2, 4]
def baseStart_451567 : Nat := 118140960795 + 451567 * 2 ^ 59
def prefixEnd_451567 : Nat := 4983230072969 + 3 ^ 40 * 451567 * 2
def baseEnd_451567 : Nat := 231870918708939975735787

theorem tailTrace_451567 : CollatzResearch.WordTrace tailWord_451567 prefixEnd_451567 231870918708939975735787 := by
  unfold tailWord_451567
  simp only [CollatzResearch.WordTrace]
  refine ⟨16470001555057355348752955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10980001036704903565835303 16470001555057355348752955)
  ·
    refine ⟨24705002332586033023129433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16470001555057355348752955 24705002332586033023129433)
    ·
      refine ⟨18528751749439524767347075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24705002332586033023129433 18528751749439524767347075)
      ·
        refine ⟨27793127624159287151020613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18528751749439524767347075 27793127624159287151020613)
        ·
          refine ⟨5211211429529866340816365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27793127624159287151020613 5211211429529866340816365)
          ·
            refine ⟨1954204286073699877806137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5211211429529866340816365 1954204286073699877806137)
            ·
              refine ⟨1465653214555274908354603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1954204286073699877806137 1465653214555274908354603)
              ·
                refine ⟨2198479821832912362531905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1465653214555274908354603 2198479821832912362531905)
                ·
                  refine ⟨1648859866374684271898929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2198479821832912362531905 1648859866374684271898929)
                  ·
                    refine ⟨1236644899781013203924197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1648859866374684271898929 1236644899781013203924197)
                    ·
                      refine ⟨231870918708939975735787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1236644899781013203924197 231870918708939975735787)
                      ·
                        rfl

theorem cell23_451567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 2, 4].length) (baseStart_451567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451567 prefixEnd_451567 := by exact prefixLift 451567
  have htrace : WordTrace (prefixWord ++ tailWord_451567) baseStart_451567 baseEnd_451567 := by
    simpa [prefixWord, tailWord_451567, baseEnd_451567] using wordTrace_append hprefix tailTrace_451567
  have hstable : (prefixWord ++ tailWord_451567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451567).length < 2 ^ (prefixWord ++ tailWord_451567).sum := by decide
  have hdescent : baseEnd_451567 < baseStart_451567 := by decide
  rcases family_descends (prefixWord ++ tailWord_451567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451572 : List Nat := [2, 6, 2, 1, 2, 1, 2, 7]
def baseStart_451572 : Nat := 118140960795 + 451572 * 2 ^ 59
def prefixEnd_451572 : Nat := 4983230072969 + 3 ^ 40 * 451572 * 2
def baseEnd_451572 : Nat := 8587906893044905784195

theorem tailTrace_451572 : CollatzResearch.WordTrace tailWord_451572 prefixEnd_451572 8587906893044905784195 := by
  unfold tailWord_451572
  simp only [CollatzResearch.WordTrace]
  refine ⟨8235091960019620601342485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10980122613359494135123313 8235091960019620601342485)
  ·
    refine ⟨386019935625919715687929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8235091960019620601342485 386019935625919715687929)
    ·
      refine ⟨289514951719439786765947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386019935625919715687929 289514951719439786765947)
      ·
        refine ⟨434272427579159680148921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289514951719439786765947 434272427579159680148921)
        ·
          refine ⟨325704320684369760111691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 434272427579159680148921 325704320684369760111691)
          ·
            refine ⟨488556481026554640167537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325704320684369760111691 488556481026554640167537)
            ·
              refine ⟨366417360769915980125653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 488556481026554640167537 366417360769915980125653)
              ·
                refine ⟨8587906893044905784195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 366417360769915980125653 8587906893044905784195)
                ·
                  rfl

theorem cell23_451572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 7].length) (baseStart_451572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451572 prefixEnd_451572 := by exact prefixLift 451572
  have htrace : WordTrace (prefixWord ++ tailWord_451572) baseStart_451572 baseEnd_451572 := by
    simpa [prefixWord, tailWord_451572, baseEnd_451572] using wordTrace_append hprefix tailTrace_451572
  have hstable : (prefixWord ++ tailWord_451572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451572).length < 2 ^ (prefixWord ++ tailWord_451572).sum := by decide
  have hdescent : baseEnd_451572 < baseStart_451572 := by decide
  rcases family_descends (prefixWord ++ tailWord_451572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451617 : List Nat := [1, 2, 3, 2, 3, 1, 1, 1, 1, 1, 7]
def baseStart_451617 : Nat := 118140960795 + 451617 * 2 ^ 59
def prefixEnd_451617 : Nat := 4983230072969 + 3 ^ 40 * 451617 * 2
def baseEnd_451617 : Nat := 231896592741664780110557

theorem tailTrace_451617 : CollatzResearch.WordTrace tailWord_451617 prefixEnd_451617 231896592741664780110557 := by
  unfold tailWord_451617
  simp only [CollatzResearch.WordTrace]
  refine ⟨16471825204876213888073105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10981216803250809258715403 16471825204876213888073105)
  ·
    refine ⟨12353868903657160416054829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16471825204876213888073105 12353868903657160416054829)
    ·
      refine ⟨4632700838871435156020561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12353868903657160416054829 4632700838871435156020561)
      ·
        refine ⟨3474525629153576367015421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4632700838871435156020561 3474525629153576367015421)
        ·
          refine ⟨1302947110932591137630783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3474525629153576367015421 1302947110932591137630783)
          ·
            refine ⟨1954420666398886706446175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1302947110932591137630783 1954420666398886706446175)
            ·
              refine ⟨2931630999598330059669263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1954420666398886706446175 2931630999598330059669263)
              ·
                refine ⟨4397446499397495089503895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2931630999598330059669263 4397446499397495089503895)
                ·
                  refine ⟨6596169749096242634255843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4397446499397495089503895 6596169749096242634255843)
                  ·
                    refine ⟨9894254623644363951383765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6596169749096242634255843 9894254623644363951383765)
                    ·
                      refine ⟨231896592741664780110557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 9894254623644363951383765 231896592741664780110557)
                      ·
                        rfl

theorem cell23_451617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_451617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451617 prefixEnd_451617 := by exact prefixLift 451617
  have htrace : WordTrace (prefixWord ++ tailWord_451617) baseStart_451617 baseEnd_451617 := by
    simpa [prefixWord, tailWord_451617, baseEnd_451617] using wordTrace_append hprefix tailTrace_451617
  have hstable : (prefixWord ++ tailWord_451617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451617).length < 2 ^ (prefixWord ++ tailWord_451617).sum := by decide
  have hdescent : baseEnd_451617 < baseStart_451617 := by decide
  rcases family_descends (prefixWord ++ tailWord_451617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451627 : List Nat := [1, 1, 1, 1, 2, 1, 5, 2, 4, 1, 4]
def baseStart_451627 : Nat := 118140960795 + 451627 * 2 ^ 59
def prefixEnd_451627 : Nat := 4983230072969 + 3 ^ 40 * 451627 * 2
def baseEnd_451627 : Nat := 231901727548209740985511

theorem tailTrace_451627 : CollatzResearch.WordTrace tailWord_451627 prefixEnd_451627 231901727548209740985511 := by
  unfold tailWord_451627
  simp only [CollatzResearch.WordTrace]
  refine ⟨16472189934839985595937135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10981459956559990397291423 16472189934839985595937135)
  ·
    refine ⟨24708284902259978393905703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16472189934839985595937135 24708284902259978393905703)
    ·
      refine ⟨37062427353389967590858555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24708284902259978393905703 37062427353389967590858555)
      ·
        refine ⟨55593641030084951386287833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37062427353389967590858555 55593641030084951386287833)
        ·
          refine ⟨41695230772563713539715875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55593641030084951386287833 41695230772563713539715875)
          ·
            refine ⟨62542846158845570309573813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41695230772563713539715875 62542846158845570309573813)
            ·
              refine ⟨5863391827391772216522545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62542846158845570309573813 5863391827391772216522545)
              ·
                refine ⟨4397543870543829162391909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5863391827391772216522545 4397543870543829162391909)
                ·
                  refine ⟨824539475726967967948483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4397543870543829162391909 824539475726967967948483)
                  ·
                    refine ⟨1236809213590451951922725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 824539475726967967948483 1236809213590451951922725)
                    ·
                      refine ⟨231901727548209740985511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1236809213590451951922725 231901727548209740985511)
                      ·
                        rfl

theorem cell23_451627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 4, 1, 4].length) (baseStart_451627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451627 prefixEnd_451627 := by exact prefixLift 451627
  have htrace : WordTrace (prefixWord ++ tailWord_451627) baseStart_451627 baseEnd_451627 := by
    simpa [prefixWord, tailWord_451627, baseEnd_451627] using wordTrace_append hprefix tailTrace_451627
  have hstable : (prefixWord ++ tailWord_451627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451627).length < 2 ^ (prefixWord ++ tailWord_451627).sum := by decide
  have hdescent : baseEnd_451627 < baseStart_451627 := by decide
  rcases family_descends (prefixWord ++ tailWord_451627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451644 : List Nat := [2, 2, 2, 2, 2, 2, 1, 3, 2, 1, 4]
def baseStart_451644 : Nat := 118140960795 + 451644 * 2 ^ 59
def prefixEnd_451644 : Nat := 4983230072969 + 3 ^ 40 * 451644 * 2
def baseEnd_451644 : Nat := 231910456719336174472933

theorem tailTrace_451644 : CollatzResearch.WordTrace tailWord_451644 prefixEnd_451644 231910456719336174472933 := by
  unfold tailWord_451644
  simp only [CollatzResearch.WordTrace]
  refine ⟨8236404987889198749652993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10981873317185598332870657 8236404987889198749652993)
  ·
    refine ⟨6177303740916899062239745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8236404987889198749652993 6177303740916899062239745)
    ·
      refine ⟨4632977805687674296679809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6177303740916899062239745 4632977805687674296679809)
      ·
        refine ⟨3474733354265755722509857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4632977805687674296679809 3474733354265755722509857)
        ·
          refine ⟨2606050015699316791882393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3474733354265755722509857 2606050015699316791882393)
          ·
            refine ⟨1954537511774487593911795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2606050015699316791882393 1954537511774487593911795)
            ·
              refine ⟨2931806267661731390867693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1954537511774487593911795 2931806267661731390867693)
              ·
                refine ⟨1099427350373149271575385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2931806267661731390867693 1099427350373149271575385)
                ·
                  refine ⟨824570512779861953681539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1099427350373149271575385 824570512779861953681539)
                  ·
                    refine ⟨1236855769169792930522309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 824570512779861953681539 1236855769169792930522309)
                    ·
                      refine ⟨231910456719336174472933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1236855769169792930522309 231910456719336174472933)
                      ·
                        rfl

theorem cell23_451644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_451644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451644 prefixEnd_451644 := by exact prefixLift 451644
  have htrace : WordTrace (prefixWord ++ tailWord_451644) baseStart_451644 baseEnd_451644 := by
    simpa [prefixWord, tailWord_451644, baseEnd_451644] using wordTrace_append hprefix tailTrace_451644
  have hstable : (prefixWord ++ tailWord_451644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451644).length < 2 ^ (prefixWord ++ tailWord_451644).sum := by decide
  have hdescent : baseEnd_451644 < baseStart_451644 := by decide
  rcases family_descends (prefixWord ++ tailWord_451644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451661 : List Nat := [1, 6, 1, 1, 1, 2, 2, 2, 2, 1, 4]
def baseStart_451661 : Nat := 118140960795 + 451661 * 2 ^ 59
def prefixEnd_451661 : Nat := 4983230072969 + 3 ^ 40 * 451661 * 2
def baseEnd_451661 : Nat := 231919185890462607960355

theorem tailTrace_451661 : CollatzResearch.WordTrace tailWord_451661 prefixEnd_451661 231919185890462607960355 := by
  unfold tailWord_451661
  simp only [CollatzResearch.WordTrace]
  refine ⟨16473430016716809402674837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10982286677811206268449891 16473430016716809402674837)
  ·
    refine ⟨772192032033600440750383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16473430016716809402674837 772192032033600440750383)
    ·
      refine ⟨1158288048050400661125575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 772192032033600440750383 1158288048050400661125575)
      ·
        refine ⟨1737432072075600991688363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1158288048050400661125575 1737432072075600991688363)
        ·
          refine ⟨2606148108113401487532545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1737432072075600991688363 2606148108113401487532545)
          ·
            refine ⟨1954611081085051115649409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2606148108113401487532545 1954611081085051115649409)
            ·
              refine ⟨1465958310813788336737057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1954611081085051115649409 1465958310813788336737057)
              ·
                refine ⟨1099468733110341252552793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1465958310813788336737057 1099468733110341252552793)
                ·
                  refine ⟨824601549832755939414595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1099468733110341252552793 824601549832755939414595)
                  ·
                    refine ⟨1236902324749133909121893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 824601549832755939414595 1236902324749133909121893)
                    ·
                      refine ⟨231919185890462607960355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1236902324749133909121893 231919185890462607960355)
                      ·
                        rfl

theorem cell23_451661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_451661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451661 prefixEnd_451661 := by exact prefixLift 451661
  have htrace : WordTrace (prefixWord ++ tailWord_451661) baseStart_451661 baseEnd_451661 := by
    simpa [prefixWord, tailWord_451661, baseEnd_451661] using wordTrace_append hprefix tailTrace_451661
  have hstable : (prefixWord ++ tailWord_451661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451661).length < 2 ^ (prefixWord ++ tailWord_451661).sum := by decide
  have hdescent : baseEnd_451661 < baseStart_451661 := by decide
  rcases family_descends (prefixWord ++ tailWord_451661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451667 : List Nat := [1, 1, 1, 2, 1, 1, 2, 8, 6]
def baseStart_451667 : Nat := 118140960795 + 451667 * 2 ^ 59
def prefixEnd_451667 : Nat := 4983230072969 + 3 ^ 40 * 451667 * 2
def baseEnd_451667 : Nat := 25769140752709953831703

theorem tailTrace_451667 : CollatzResearch.WordTrace tailWord_451667 prefixEnd_451667 25769140752709953831703 := by
  unfold tailWord_451667
  simp only [CollatzResearch.WordTrace]
  refine ⟨16473648854695072427393255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10982432569796714951595503 16473648854695072427393255)
  ·
    refine ⟨24710473282042608641089883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16473648854695072427393255 24710473282042608641089883)
    ·
      refine ⟨37065709923063912961634825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24710473282042608641089883 37065709923063912961634825)
      ·
        refine ⟨27799282442297934721226119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37065709923063912961634825 27799282442297934721226119)
        ·
          refine ⟨41698923663446902081839179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27799282442297934721226119 41698923663446902081839179)
          ·
            refine ⟨62548385495170353122758769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41698923663446902081839179 62548385495170353122758769)
            ·
              refine ⟨46911289121377764842069077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62548385495170353122758769 46911289121377764842069077)
              ·
                refine ⟨549741669391145681742997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 46911289121377764842069077 549741669391145681742997)
                ·
                  refine ⟨25769140752709953831703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 549741669391145681742997 25769140752709953831703)
                  ·
                    rfl

theorem cell23_451667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 8, 6].length) (baseStart_451667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451667 prefixEnd_451667 := by exact prefixLift 451667
  have htrace : WordTrace (prefixWord ++ tailWord_451667) baseStart_451667 baseEnd_451667 := by
    simpa [prefixWord, tailWord_451667, baseEnd_451667] using wordTrace_append hprefix tailTrace_451667
  have hstable : (prefixWord ++ tailWord_451667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451667).length < 2 ^ (prefixWord ++ tailWord_451667).sum := by decide
  have hdescent : baseEnd_451667 < baseStart_451667 := by decide
  rcases family_descends (prefixWord ++ tailWord_451667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451688 : List Nat := [2, 1, 4, 4, 1, 1, 1, 2, 3, 4]
def baseStart_451688 : Nat := 118140960795 + 451688 * 2 ^ 59
def prefixEnd_451688 : Nat := 4983230072969 + 3 ^ 40 * 451688 * 2
def baseEnd_451688 : Nat := 77311016622711334107577

theorem tailTrace_451688 : CollatzResearch.WordTrace tailWord_451688 prefixEnd_451688 77311016622711334107577 := by
  unfold tailWord_451688
  simp only [CollatzResearch.WordTrace]
  refine ⟨8237207393809496506953859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10982943191745995342605145 8237207393809496506953859)
  ·
    refine ⟨12355811090714244760430789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8237207393809496506953859 12355811090714244760430789)
    ·
      refine ⟨2316714579508920892580773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12355811090714244760430789 2316714579508920892580773)
      ·
        refine ⟨434383983657922667358895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2316714579508920892580773 434383983657922667358895)
        ·
          refine ⟨651575975486884001038343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434383983657922667358895 651575975486884001038343)
          ·
            refine ⟨977363963230326001557515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 651575975486884001038343 977363963230326001557515)
            ·
              refine ⟨1466045944845489002336273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 977363963230326001557515 1466045944845489002336273)
              ·
                refine ⟨1099534458634116751752205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1466045944845489002336273 1099534458634116751752205)
                ·
                  refine ⟨412325421987793781907077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1099534458634116751752205 412325421987793781907077)
                  ·
                    refine ⟨77311016622711334107577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 412325421987793781907077 77311016622711334107577)
                    ·
                      rfl

theorem cell23_451688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_451688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451688 prefixEnd_451688 := by exact prefixLift 451688
  have htrace : WordTrace (prefixWord ++ tailWord_451688) baseStart_451688 baseEnd_451688 := by
    simpa [prefixWord, tailWord_451688, baseEnd_451688] using wordTrace_append hprefix tailTrace_451688
  have hstable : (prefixWord ++ tailWord_451688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451688).length < 2 ^ (prefixWord ++ tailWord_451688).sum := by decide
  have hdescent : baseEnd_451688 < baseStart_451688 := by decide
  rcases family_descends (prefixWord ++ tailWord_451688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451761 : List Nat := [1, 2, 2, 5, 1, 1, 1, 2, 4, 4]
def baseStart_451761 : Nat := 118140960795 + 451761 * 2 ^ 59
def prefixEnd_451761 : Nat := 4983230072969 + 3 ^ 40 * 451761 * 2
def baseEnd_451761 : Nat := 77323511318637405569965

theorem tailTrace_451761 : CollatzResearch.WordTrace tailWord_451761 prefixEnd_451761 77323511318637405569965 := by
  unfold tailWord_451761
  simp only [CollatzResearch.WordTrace]
  refine ⟨16477077316354526481315137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10984718210903017654210091 16477077316354526481315137)
  ·
    refine ⟨12357807987265894860986353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16477077316354526481315137 12357807987265894860986353)
    ·
      refine ⟨9268355990449421145739765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12357807987265894860986353 9268355990449421145739765)
      ·
        refine ⟨868908374104633232413103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9268355990449421145739765 868908374104633232413103)
        ·
          refine ⟨1303362561156949848619655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 868908374104633232413103 1303362561156949848619655)
          ·
            refine ⟨1955043841735424772929483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1303362561156949848619655 1955043841735424772929483)
            ·
              refine ⟨2932565762603137159394225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1955043841735424772929483 2932565762603137159394225)
              ·
                refine ⟨2199424321952352869545669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2932565762603137159394225 2199424321952352869545669)
                ·
                  refine ⟨412392060366066163039813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2199424321952352869545669 412392060366066163039813)
                  ·
                    refine ⟨77323511318637405569965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 412392060366066163039813 77323511318637405569965)
                    ·
                      rfl

theorem cell23_451761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 4, 4].length) (baseStart_451761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451761 prefixEnd_451761 := by exact prefixLift 451761
  have htrace : WordTrace (prefixWord ++ tailWord_451761) baseStart_451761 baseEnd_451761 := by
    simpa [prefixWord, tailWord_451761, baseEnd_451761] using wordTrace_append hprefix tailTrace_451761
  have hstable : (prefixWord ++ tailWord_451761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451761).length < 2 ^ (prefixWord ++ tailWord_451761).sum := by decide
  have hdescent : baseEnd_451761 < baseStart_451761 := by decide
  rcases family_descends (prefixWord ++ tailWord_451761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451774 : List Nat := [4, 2, 1, 1, 3, 1, 11]
def baseStart_451774 : Nat := 118140960795 + 451774 * 2 ^ 59
def prefixEnd_451774 : Nat := 4983230072969 + 3 ^ 40 * 451774 * 2
def baseEnd_451774 : Nat := 2863916163017539084535

theorem tailTrace_451774 : CollatzResearch.WordTrace tailWord_451774 prefixEnd_451774 2863916163017539084535 := by
  unfold tailWord_451774
  simp only [CollatzResearch.WordTrace]
  refine ⟨2059693933163428712692297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10985034310204953134358917 2059693933163428712692297)
  ·
    refine ⟨1544770449872571534519223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2059693933163428712692297 1544770449872571534519223)
    ·
      refine ⟨2317155674808857301778835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1544770449872571534519223 2317155674808857301778835)
      ·
        refine ⟨3475733512213285952668253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2317155674808857301778835 3475733512213285952668253)
        ·
          refine ⟨1303400067079982232250595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3475733512213285952668253 1303400067079982232250595)
          ·
            refine ⟨1955100100619973348375893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1303400067079982232250595 1955100100619973348375893)
            ·
              refine ⟨2863916163017539084535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 1955100100619973348375893 2863916163017539084535)
              ·
                rfl

theorem cell23_451774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 11].length) (baseStart_451774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451774 prefixEnd_451774 := by exact prefixLift 451774
  have htrace : WordTrace (prefixWord ++ tailWord_451774) baseStart_451774 baseEnd_451774 := by
    simpa [prefixWord, tailWord_451774, baseEnd_451774] using wordTrace_append hprefix tailTrace_451774
  have hstable : (prefixWord ++ tailWord_451774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451774).length < 2 ^ (prefixWord ++ tailWord_451774).sum := by decide
  have hdescent : baseEnd_451774 < baseStart_451774 := by decide
  rcases family_descends (prefixWord ++ tailWord_451774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451794 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 2, 2, 6]
def baseStart_451794 : Nat := 118140960795 + 451794 * 2 ^ 59
def prefixEnd_451794 : Nat := 4983230072969 + 3 ^ 40 * 451794 * 2
def baseEnd_451794 : Nat := 231987478817510587597243

theorem tailTrace_451794 : CollatzResearch.WordTrace tailWord_451794 prefixEnd_451794 231987478817510587597243 := by
  unfold tailWord_451794
  simp only [CollatzResearch.WordTrace]
  refine ⟨4119570231308743279316609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10985520616823315411510957 4119570231308743279316609)
  ·
    refine ⟨3089677673481557459487457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4119570231308743279316609 3089677673481557459487457)
    ·
      refine ⟨2317258255111168094615593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3089677673481557459487457 2317258255111168094615593)
      ·
        refine ⟨1737943691333376070961695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2317258255111168094615593 1737943691333376070961695)
        ·
          refine ⟨2606915537000064106442543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1737943691333376070961695 2606915537000064106442543)
          ·
            refine ⟨3910373305500096159663815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2606915537000064106442543 3910373305500096159663815)
            ·
              refine ⟨5865559958250144239495723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3910373305500096159663815 5865559958250144239495723)
              ·
                refine ⟨8798339937375216359243585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5865559958250144239495723 8798339937375216359243585)
                ·
                  refine ⟨6598754953031412269432689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8798339937375216359243585 6598754953031412269432689)
                  ·
                    refine ⟨4949066214773559202074517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6598754953031412269432689 4949066214773559202074517)
                    ·
                      refine ⟨231987478817510587597243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4949066214773559202074517 231987478817510587597243)
                      ·
                        rfl

theorem cell23_451794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_451794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451794 prefixEnd_451794 := by exact prefixLift 451794
  have htrace : WordTrace (prefixWord ++ tailWord_451794) baseStart_451794 baseEnd_451794 := by
    simpa [prefixWord, tailWord_451794, baseEnd_451794] using wordTrace_append hprefix tailTrace_451794
  have hstable : (prefixWord ++ tailWord_451794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451794).length < 2 ^ (prefixWord ++ tailWord_451794).sum := by decide
  have hdescent : baseEnd_451794 < baseStart_451794 := by decide
  rcases family_descends (prefixWord ++ tailWord_451794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451834 : List Nat := [3, 1, 1, 1, 1, 4, 2, 2, 2, 6]
def baseStart_451834 : Nat := 118140960795 + 451834 * 2 ^ 59
def prefixEnd_451834 : Nat := 4983230072969 + 3 ^ 40 * 451834 * 2
def baseEnd_451834 : Nat := 77336006014563477032353

theorem tailTrace_451834 : CollatzResearch.WordTrace tailWord_451834 prefixEnd_451834 77336006014563477032353 := by
  unfold tailWord_451834
  simp only [CollatzResearch.WordTrace]
  refine ⟨4119934961272514987180639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10986493230060039965815037 4119934961272514987180639)
  ·
    refine ⟨6179902441908772480770959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4119934961272514987180639 6179902441908772480770959)
    ·
      refine ⟨9269853662863158721156439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6179902441908772480770959 9269853662863158721156439)
      ·
        refine ⟨13904780494294738081734659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9269853662863158721156439 13904780494294738081734659)
        ·
          refine ⟨20857170741442107122601989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13904780494294738081734659 20857170741442107122601989)
          ·
            refine ⟨3910719514020395085487873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20857170741442107122601989 3910719514020395085487873)
            ·
              refine ⟨2933039635515296314115905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3910719514020395085487873 2933039635515296314115905)
              ·
                refine ⟨2199779726636472235586929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2933039635515296314115905 2199779726636472235586929)
                ·
                  refine ⟨1649834794977354176690197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2199779726636472235586929 1649834794977354176690197)
                  ·
                    refine ⟨77336006014563477032353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1649834794977354176690197 77336006014563477032353)
                    ·
                      rfl

theorem cell23_451834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 2, 6].length) (baseStart_451834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451834 prefixEnd_451834 := by exact prefixLift 451834
  have htrace : WordTrace (prefixWord ++ tailWord_451834) baseStart_451834 baseEnd_451834 := by
    simpa [prefixWord, tailWord_451834, baseEnd_451834] using wordTrace_append hprefix tailTrace_451834
  have hstable : (prefixWord ++ tailWord_451834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451834).length < 2 ^ (prefixWord ++ tailWord_451834).sum := by decide
  have hdescent : baseEnd_451834 < baseStart_451834 := by decide
  rcases family_descends (prefixWord ++ tailWord_451834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451836 : List Nat := [2, 2, 2, 1, 6, 1, 2, 2, 1, 2, 2]
def baseStart_451836 : Nat := 118140960795 + 451836 * 2 ^ 59
def prefixEnd_451836 : Nat := 4983230072969 + 3 ^ 40 * 451836 * 2
def baseEnd_451836 : Nat := 232009045004999423272051

theorem tailTrace_451836 : CollatzResearch.WordTrace tailWord_451836 prefixEnd_451836 232009045004999423272051 := by
  unfold tailWord_451836
  simp only [CollatzResearch.WordTrace]
  refine ⟨8239906395541407145147681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10986541860721876193530241 8239906395541407145147681)
  ·
    refine ⟨6179929796656055358860761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8239906395541407145147681 6179929796656055358860761)
    ·
      refine ⟨4634947347492041519145571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6179929796656055358860761 4634947347492041519145571)
      ·
        refine ⟨6952421021238062278718357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4634947347492041519145571 6952421021238062278718357)
        ·
          refine ⟨325894735370534169314923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6952421021238062278718357 325894735370534169314923)
          ·
            refine ⟨488842103055801253972385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325894735370534169314923 488842103055801253972385)
            ·
              refine ⟨366631577291850940479289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 488842103055801253972385 366631577291850940479289)
              ·
                refine ⟨274973682968888205359467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 366631577291850940479289 274973682968888205359467)
                ·
                  refine ⟨412460524453332308039201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 274973682968888205359467 412460524453332308039201)
                  ·
                    refine ⟨309345393339999231029401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 412460524453332308039201 309345393339999231029401)
                    ·
                      refine ⟨232009045004999423272051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 309345393339999231029401 232009045004999423272051)
                      ·
                        rfl

theorem cell23_451836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 2, 1, 2, 2].length) (baseStart_451836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451836 prefixEnd_451836 := by exact prefixLift 451836
  have htrace : WordTrace (prefixWord ++ tailWord_451836) baseStart_451836 baseEnd_451836 := by
    simpa [prefixWord, tailWord_451836, baseEnd_451836] using wordTrace_append hprefix tailTrace_451836
  have hstable : (prefixWord ++ tailWord_451836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451836).length < 2 ^ (prefixWord ++ tailWord_451836).sum := by decide
  have hdescent : baseEnd_451836 < baseStart_451836 := by decide
  rcases family_descends (prefixWord ++ tailWord_451836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451864 : List Nat := [2, 1, 2, 3, 1, 3, 1, 1, 9]
def baseStart_451864 : Nat := 118140960795 + 451864 * 2 ^ 59
def prefixEnd_451864 : Nat := 4983230072969 + 3 ^ 40 * 451864 * 2
def baseEnd_451864 : Nat := 25780380273702812635769

theorem tailTrace_451864 : CollatzResearch.WordTrace tailWord_451864 prefixEnd_451864 25780380273702812635769 := by
  unfold tailWord_451864
  simp only [CollatzResearch.WordTrace]
  refine ⟨8240417017490687536157323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10987222689987583381543097 8240417017490687536157323)
  ·
    refine ⟨12360625526236031304235985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8240417017490687536157323 12360625526236031304235985)
    ·
      refine ⟨9270469144677023478176989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12360625526236031304235985 9270469144677023478176989)
      ·
        refine ⟨3476425929253883804316371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9270469144677023478176989 3476425929253883804316371)
        ·
          refine ⟨5214638893880825706474557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3476425929253883804316371 5214638893880825706474557)
          ·
            refine ⟨1955489585205309639927959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5214638893880825706474557 1955489585205309639927959)
            ·
              refine ⟨2933234377807964459891939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1955489585205309639927959 2933234377807964459891939)
              ·
                refine ⟨4399851566711946689837909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2933234377807964459891939 4399851566711946689837909)
                ·
                  refine ⟨25780380273702812635769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4399851566711946689837909 25780380273702812635769)
                  ·
                    rfl

theorem cell23_451864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 9].length) (baseStart_451864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451864 prefixEnd_451864 := by exact prefixLift 451864
  have htrace : WordTrace (prefixWord ++ tailWord_451864) baseStart_451864 baseEnd_451864 := by
    simpa [prefixWord, tailWord_451864, baseEnd_451864] using wordTrace_append hprefix tailTrace_451864
  have hstable : (prefixWord ++ tailWord_451864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451864).length < 2 ^ (prefixWord ++ tailWord_451864).sum := by decide
  have hdescent : baseEnd_451864 < baseStart_451864 := by decide
  rcases family_descends (prefixWord ++ tailWord_451864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451891 : List Nat := [1, 1, 1, 2, 5, 2, 1, 2, 2, 3, 3]
def baseStart_451891 : Nat := 118140960795 + 451891 * 2 ^ 59
def prefixEnd_451891 : Nat := 4983230072969 + 3 ^ 40 * 451891 * 2
def baseEnd_451891 : Nat := 232037286440996708084297

theorem tailTrace_451891 : CollatzResearch.WordTrace tailWord_451891 prefixEnd_451891 232037286440996708084297 := by
  unfold tailWord_451891
  simp only [CollatzResearch.WordTrace]
  refine ⟨16481818805883558683547527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10987879203922372455698351 16481818805883558683547527)
  ·
    refine ⟨24722728208825338025321291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16481818805883558683547527 24722728208825338025321291)
    ·
      refine ⟨37084092313238007037981937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24722728208825338025321291 37084092313238007037981937)
      ·
        refine ⟨27813069234928505278486453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37084092313238007037981937 27813069234928505278486453)
        ·
          refine ⟨2607475240774547369858105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27813069234928505278486453 2607475240774547369858105)
          ·
            refine ⟨1955606430580910527393579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2607475240774547369858105 1955606430580910527393579)
            ·
              refine ⟨2933409645871365791090369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1955606430580910527393579 2933409645871365791090369)
              ·
                refine ⟨2200057234403524343317777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2933409645871365791090369 2200057234403524343317777)
                ·
                  refine ⟨1650042925802643257488333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2200057234403524343317777 1650042925802643257488333)
                  ·
                    refine ⟨618766097175991221558125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1650042925802643257488333 618766097175991221558125)
                    ·
                      refine ⟨232037286440996708084297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 618766097175991221558125 232037286440996708084297)
                      ·
                        rfl

theorem cell23_451891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 3, 3].length) (baseStart_451891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451891 prefixEnd_451891 := by exact prefixLift 451891
  have htrace : WordTrace (prefixWord ++ tailWord_451891) baseStart_451891 baseEnd_451891 := by
    simpa [prefixWord, tailWord_451891, baseEnd_451891] using wordTrace_append hprefix tailTrace_451891
  have hstable : (prefixWord ++ tailWord_451891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451891).length < 2 ^ (prefixWord ++ tailWord_451891).sum := by decide
  have hdescent : baseEnd_451891 < baseStart_451891 := by decide
  rcases family_descends (prefixWord ++ tailWord_451891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451904 : List Nat := [2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 7]
def baseStart_451904 : Nat := 118140960795 + 451904 * 2 ^ 59
def prefixEnd_451904 : Nat := 4983230072969 + 3 ^ 40 * 451904 * 2
def baseEnd_451904 : Nat := 232043961689505157221737

theorem tailTrace_451904 : CollatzResearch.WordTrace tailWord_451904 prefixEnd_451904 232043961689505157221737 := by
  unfold tailWord_451904
  simp only [CollatzResearch.WordTrace]
  refine ⟨8241146477418230951885383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10988195303224307935847177 8241146477418230951885383)
  ·
    refine ⟨12361719716127346427828075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8241146477418230951885383 12361719716127346427828075)
    ·
      refine ⟨18542579574191019641742113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12361719716127346427828075 18542579574191019641742113)
      ·
        refine ⟨13906934680643264731306585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18542579574191019641742113 13906934680643264731306585)
        ·
          refine ⟨10430201010482448548479939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13906934680643264731306585 10430201010482448548479939)
          ·
            refine ⟨15645301515723672822719909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10430201010482448548479939 15645301515723672822719909)
            ·
              refine ⟨2933494034198188654259983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15645301515723672822719909 2933494034198188654259983)
              ·
                refine ⟨4400241051297282981389975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2933494034198188654259983 4400241051297282981389975)
                ·
                  refine ⟨6600361576945924472084963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4400241051297282981389975 6600361576945924472084963)
                  ·
                    refine ⟨9900542365418886708127445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6600361576945924472084963 9900542365418886708127445)
                    ·
                      refine ⟨232043961689505157221737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 9900542365418886708127445 232043961689505157221737)
                      ·
                        rfl

theorem cell23_451904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_451904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451904 prefixEnd_451904 := by exact prefixLift 451904
  have htrace : WordTrace (prefixWord ++ tailWord_451904) baseStart_451904 baseEnd_451904 := by
    simpa [prefixWord, tailWord_451904, baseEnd_451904] using wordTrace_append hprefix tailTrace_451904
  have hstable : (prefixWord ++ tailWord_451904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451904).length < 2 ^ (prefixWord ++ tailWord_451904).sum := by decide
  have hdescent : baseEnd_451904 < baseStart_451904 := by decide
  rcases family_descends (prefixWord ++ tailWord_451904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451948 : List Nat := [2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 4]
def baseStart_451948 : Nat := 118140960795 + 451948 * 2 ^ 59
def prefixEnd_451948 : Nat := 4983230072969 + 3 ^ 40 * 451948 * 2
def baseEnd_451948 : Nat := 232066554838302985071535

theorem tailTrace_451948 : CollatzResearch.WordTrace tailWord_451948 prefixEnd_451948 232066554838302985071535 := by
  unfold tailWord_451948
  simp only [CollatzResearch.WordTrace]
  refine ⟨8241948883338528709186249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10989265177784704945581665 8241948883338528709186249)
  ·
    refine ⟨6181461662503896531889687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8241948883338528709186249 6181461662503896531889687)
    ·
      refine ⟨9272192493755844797834531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6181461662503896531889687 9272192493755844797834531)
      ·
        refine ⟨13908288740633767196751797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9272192493755844797834531 13908288740633767196751797)
        ·
          refine ⟨1303902069434415674695481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13908288740633767196751797 1303902069434415674695481)
          ·
            refine ⟨977926552075811756021611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1303902069434415674695481 977926552075811756021611)
            ·
              refine ⟨1466889828113717634032417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 977926552075811756021611 1466889828113717634032417)
              ·
                refine ⟨1100167371085288225524313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1466889828113717634032417 1100167371085288225524313)
                ·
                  refine ⟨825125528313966169143235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1100167371085288225524313 825125528313966169143235)
                  ·
                    refine ⟨1237688292470949253714853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 825125528313966169143235 1237688292470949253714853)
                    ·
                      refine ⟨232066554838302985071535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1237688292470949253714853 232066554838302985071535)
                      ·
                        rfl

theorem cell23_451948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 4].length) (baseStart_451948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_451948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_451948 prefixEnd_451948 := by exact prefixLift 451948
  have htrace : WordTrace (prefixWord ++ tailWord_451948) baseStart_451948 baseEnd_451948 := by
    simpa [prefixWord, tailWord_451948, baseEnd_451948] using wordTrace_append hprefix tailTrace_451948
  have hstable : (prefixWord ++ tailWord_451948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451948).length < 2 ^ (prefixWord ++ tailWord_451948).sum := by decide
  have hdescent : baseEnd_451948 < baseStart_451948 := by decide
  rcases family_descends (prefixWord ++ tailWord_451948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452042 : List Nat := [3, 1, 2, 1, 2, 5, 1, 1, 2, 3, 2]
def baseStart_452042 : Nat := 118140960795 + 452042 * 2 ^ 59
def prefixEnd_452042 : Nat := 4983230072969 + 3 ^ 40 * 452042 * 2
def baseEnd_452042 : Nat := 232114822019825617296103

theorem tailTrace_452042 : CollatzResearch.WordTrace tailWord_452042 prefixEnd_452042 232114822019825617296103 := by
  unfold tailWord_452042
  simp only [CollatzResearch.WordTrace]
  refine ⟨4121831557084127868073595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10991550818891007648196253 4121831557084127868073595)
  ·
    refine ⟨6182747335626191802110393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4121831557084127868073595 6182747335626191802110393)
    ·
      refine ⟨4637060501719643851582795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6182747335626191802110393 4637060501719643851582795)
      ·
        refine ⟨6955590752579465777374193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4637060501719643851582795 6955590752579465777374193)
        ·
          refine ⟨5216693064434599333030645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6955590752579465777374193 5216693064434599333030645)
          ·
            refine ⟨489064974790743687471623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5216693064434599333030645 489064974790743687471623)
            ·
              refine ⟨733597462186115531207435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 489064974790743687471623 733597462186115531207435)
              ·
                refine ⟨1100396193279173296811153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 733597462186115531207435 1100396193279173296811153)
                ·
                  refine ⟨825297144959379972608365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1100396193279173296811153 825297144959379972608365)
                  ·
                    refine ⟨309486429359767489728137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 825297144959379972608365 309486429359767489728137)
                    ·
                      refine ⟨232114822019825617296103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 309486429359767489728137 232114822019825617296103)
                      ·
                        rfl

theorem cell23_452042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 2, 3, 2].length) (baseStart_452042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_452042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_452042 prefixEnd_452042 := by exact prefixLift 452042
  have htrace : WordTrace (prefixWord ++ tailWord_452042) baseStart_452042 baseEnd_452042 := by
    simpa [prefixWord, tailWord_452042, baseEnd_452042] using wordTrace_append hprefix tailTrace_452042
  have hstable : (prefixWord ++ tailWord_452042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452042).length < 2 ^ (prefixWord ++ tailWord_452042).sum := by decide
  have hdescent : baseEnd_452042 < baseStart_452042 := by decide
  rcases family_descends (prefixWord ++ tailWord_452042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452065 : List Nat := [1, 2, 3, 1, 2, 3, 3, 2, 2, 4]
def baseStart_452065 : Nat := 118140960795 + 452065 * 2 ^ 59
def prefixEnd_452065 : Nat := 4983230072969 + 3 ^ 40 * 452065 * 2
def baseEnd_452065 : Nat := 77375544024959675769499

theorem tailTrace_452065 : CollatzResearch.WordTrace tailWord_452065 prefixEnd_452065 77375544024959675769499 := by
  unfold tailWord_452065
  simp only [CollatzResearch.WordTrace]
  refine ⟨16488165107253186400381649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10992110071502124266921099 16488165107253186400381649)
  ·
    refine ⟨12366123830439889800286237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16488165107253186400381649 12366123830439889800286237)
    ·
      refine ⟨4637296436414958675107339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12366123830439889800286237 4637296436414958675107339)
      ·
        refine ⟨6955944654622438012661009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4637296436414958675107339 6955944654622438012661009)
        ·
          refine ⟨5216958490966828509495757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6955944654622438012661009 5216958490966828509495757)
          ·
            refine ⟨1956359434112560691060909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5216958490966828509495757 1956359434112560691060909)
            ·
              refine ⟨733634787792210259147841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1956359434112560691060909 733634787792210259147841)
              ·
                refine ⟨550226090844157694360881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 733634787792210259147841 550226090844157694360881)
                ·
                  refine ⟨412669568133118270770661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 550226090844157694360881 412669568133118270770661)
                  ·
                    refine ⟨77375544024959675769499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 412669568133118270770661 77375544024959675769499)
                    ·
                      rfl

theorem cell23_452065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2, 2, 4].length) (baseStart_452065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_452065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_452065 prefixEnd_452065 := by exact prefixLift 452065
  have htrace : WordTrace (prefixWord ++ tailWord_452065) baseStart_452065 baseEnd_452065 := by
    simpa [prefixWord, tailWord_452065, baseEnd_452065] using wordTrace_append hprefix tailTrace_452065
  have hstable : (prefixWord ++ tailWord_452065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452065).length < 2 ^ (prefixWord ++ tailWord_452065).sum := by decide
  have hdescent : baseEnd_452065 < baseStart_452065 := by decide
  rcases family_descends (prefixWord ++ tailWord_452065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452072 : List Nat := [2, 1, 4, 1, 1, 2, 4, 1, 3, 2, 2]
def baseStart_452072 : Nat := 118140960795 + 452072 * 2 ^ 59
def prefixEnd_452072 : Nat := 4983230072969 + 3 ^ 40 * 452072 * 2
def baseEnd_452072 : Nat := 232130226439460499920965

theorem tailTrace_452072 : CollatzResearch.WordTrace tailWord_452072 prefixEnd_452072 232130226439460499920965 := by
  unfold tailWord_452072
  simp only [CollatzResearch.WordTrace]
  refine ⟨8244210209113913297943235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10992280278818551063924313 8244210209113913297943235)
  ·
    refine ⟨12366315313670869946914853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8244210209113913297943235 12366315313670869946914853)
    ·
      refine ⟨2318684121313288115046535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12366315313670869946914853 2318684121313288115046535)
      ·
        refine ⟨3478026181969932172569803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2318684121313288115046535 3478026181969932172569803)
        ·
          refine ⟨5217039272954898258854705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3478026181969932172569803 5217039272954898258854705)
          ·
            refine ⟨3912779454716173694141029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5217039272954898258854705 3912779454716173694141029)
            ·
              refine ⟨733646147759282567651443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3912779454716173694141029 733646147759282567651443)
              ·
                refine ⟨1100469221638923851477165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 733646147759282567651443 1100469221638923851477165)
                ·
                  refine ⟨412675958114596444303937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1100469221638923851477165 412675958114596444303937)
                  ·
                    refine ⟨309506968585947333227953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 412675958114596444303937 309506968585947333227953)
                    ·
                      refine ⟨232130226439460499920965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 309506968585947333227953 232130226439460499920965)
                      ·
                        rfl

theorem cell23_452072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 3, 2, 2].length) (baseStart_452072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_452072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_452072 prefixEnd_452072 := by exact prefixLift 452072
  have htrace : WordTrace (prefixWord ++ tailWord_452072) baseStart_452072 baseEnd_452072 := by
    simpa [prefixWord, tailWord_452072, baseEnd_452072] using wordTrace_append hprefix tailTrace_452072
  have hstable : (prefixWord ++ tailWord_452072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452072).length < 2 ^ (prefixWord ++ tailWord_452072).sum := by decide
  have hdescent : baseEnd_452072 < baseStart_452072 := by decide
  rcases family_descends (prefixWord ++ tailWord_452072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452085 : List Nat := [1, 3, 5, 1, 1, 2, 1, 1, 1, 1, 6]
def baseStart_452085 : Nat := 118140960795 + 452085 * 2 ^ 59
def prefixEnd_452085 : Nat := 4983230072969 + 3 ^ 40 * 452085 * 2
def baseEnd_452085 : Nat := 232136901687968949058405

theorem tailTrace_452085 : CollatzResearch.WordTrace tailWord_452085 prefixEnd_452085 232136901687968949058405 := by
  unfold tailWord_452085
  simp only [CollatzResearch.WordTrace]
  refine ⟨16488894567180729816109709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10992596378120486544073139 16488894567180729816109709)
  ·
    refine ⟨6183335462692773681041141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16488894567180729816109709 6183335462692773681041141)
    ·
      refine ⟨579687699627447532597607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6183335462692773681041141 579687699627447532597607)
      ·
        refine ⟨869531549441171298896411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 579687699627447532597607 869531549441171298896411)
        ·
          refine ⟨1304297324161756948344617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 869531549441171298896411 1304297324161756948344617)
          ·
            refine ⟨978222993121317711258463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1304297324161756948344617 978222993121317711258463)
            ·
              refine ⟨1467334489681976566887695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 978222993121317711258463 1467334489681976566887695)
              ·
                refine ⟨2201001734522964850331543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1467334489681976566887695 2201001734522964850331543)
                ·
                  refine ⟨3301502601784447275497315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2201001734522964850331543 3301502601784447275497315)
                  ·
                    refine ⟨4952253902676670913245973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3301502601784447275497315 4952253902676670913245973)
                    ·
                      refine ⟨232136901687968949058405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4952253902676670913245973 232136901687968949058405)
                      ·
                        rfl

theorem cell23_452085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_452085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_452085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_452085 prefixEnd_452085 := by exact prefixLift 452085
  have htrace : WordTrace (prefixWord ++ tailWord_452085) baseStart_452085 baseEnd_452085 := by
    simpa [prefixWord, tailWord_452085, baseEnd_452085] using wordTrace_append hprefix tailTrace_452085
  have hstable : (prefixWord ++ tailWord_452085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452085).length < 2 ^ (prefixWord ++ tailWord_452085).sum := by decide
  have hdescent : baseEnd_452085 < baseStart_452085 := by decide
  rcases family_descends (prefixWord ++ tailWord_452085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452106 : List Nat := [3, 1, 2, 2, 2, 4, 1, 3, 1, 2, 2]
def baseStart_452106 : Nat := 118140960795 + 452106 * 2 ^ 59
def prefixEnd_452106 : Nat := 4983230072969 + 3 ^ 40 * 452106 * 2
def baseEnd_452106 : Nat := 232147684781713366895809

theorem tailTrace_452106 : CollatzResearch.WordTrace tailWord_452106 prefixEnd_452106 232147684781713366895809 := by
  unfold tailWord_452106
  simp only [CollatzResearch.WordTrace]
  refine ⟨4122415125026162600656043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10993107000069766935082781 4122415125026162600656043)
  ·
    refine ⟨6183622687539243900984065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4122415125026162600656043 6183622687539243900984065)
    ·
      refine ⟨4637717015654432925738049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6183622687539243900984065 4637717015654432925738049)
      ·
        refine ⟨3478287761740824694303537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4637717015654432925738049 3478287761740824694303537)
        ·
          refine ⟨2608715821305618520727653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3478287761740824694303537 2608715821305618520727653)
          ·
            refine ⟨489134216494803472636435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2608715821305618520727653 489134216494803472636435)
            ·
              refine ⟨733701324742205208954653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 489134216494803472636435 733701324742205208954653)
              ·
                refine ⟨275137996778326953357995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 733701324742205208954653 275137996778326953357995)
                ·
                  refine ⟨412706995167490430036993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 275137996778326953357995 412706995167490430036993)
                  ·
                    refine ⟨309530246375617822527745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 412706995167490430036993 309530246375617822527745)
                    ·
                      refine ⟨232147684781713366895809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 309530246375617822527745 232147684781713366895809)
                      ·
                        rfl

theorem cell23_452106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 3, 1, 2, 2].length) (baseStart_452106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_452106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_452106 prefixEnd_452106 := by exact prefixLift 452106
  have htrace : WordTrace (prefixWord ++ tailWord_452106) baseStart_452106 baseEnd_452106 := by
    simpa [prefixWord, tailWord_452106, baseEnd_452106] using wordTrace_append hprefix tailTrace_452106
  have hstable : (prefixWord ++ tailWord_452106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452106).length < 2 ^ (prefixWord ++ tailWord_452106).sum := by decide
  have hdescent : baseEnd_452106 < baseStart_452106 := by decide
  rcases family_descends (prefixWord ++ tailWord_452106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452109 : List Nat := [1, 7, 1, 1, 2, 1, 2, 1, 1, 1, 5]
def baseStart_452109 : Nat := 118140960795 + 452109 * 2 ^ 59
def prefixEnd_452109 : Nat := 4983230072969 + 3 ^ 40 * 452109 * 2
def baseEnd_452109 : Nat := 232149225223676855158295

theorem tailTrace_452109 : CollatzResearch.WordTrace tailWord_452109 prefixEnd_452109 232149225223676855158295 := by
  unfold tailWord_452109
  simp only [CollatzResearch.WordTrace]
  refine ⟨16489769919093781914983381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10993179946062521276655587 16489769919093781914983381)
  ·
    refine ⟨386478982478760513632423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 16489769919093781914983381 386478982478760513632423)
    ·
      refine ⟨579718473718140770448635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386478982478760513632423 579718473718140770448635)
      ·
        refine ⟨869577710577211155672953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 579718473718140770448635 869577710577211155672953)
        ·
          refine ⟨652183282932908366754715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 869577710577211155672953 652183282932908366754715)
          ·
            refine ⟨978274924399362550132073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652183282932908366754715 978274924399362550132073)
            ·
              refine ⟨733706193299521912599055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 978274924399362550132073 733706193299521912599055)
              ·
                refine ⟨1100559289949282868898583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 733706193299521912599055 1100559289949282868898583)
                ·
                  refine ⟨1650838934923924303347875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1100559289949282868898583 1650838934923924303347875)
                  ·
                    refine ⟨2476258402385886455021813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1650838934923924303347875 2476258402385886455021813)
                    ·
                      refine ⟨232149225223676855158295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2476258402385886455021813 232149225223676855158295)
                      ·
                        rfl

theorem cell23_452109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_452109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_452109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_452109 prefixEnd_452109 := by exact prefixLift 452109
  have htrace : WordTrace (prefixWord ++ tailWord_452109) baseStart_452109 baseEnd_452109 := by
    simpa [prefixWord, tailWord_452109, baseEnd_452109] using wordTrace_append hprefix tailTrace_452109
  have hstable : (prefixWord ++ tailWord_452109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452109).length < 2 ^ (prefixWord ++ tailWord_452109).sum := by decide
  have hdescent : baseEnd_452109 < baseStart_452109 := by decide
  rcases family_descends (prefixWord ++ tailWord_452109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452138 : List Nat := [3, 1, 4, 1, 1, 1, 2, 1, 1, 8]
def baseStart_452138 : Nat := 118140960795 + 452138 * 2 ^ 59
def prefixEnd_452138 : Nat := 4983230072969 + 3 ^ 40 * 452138 * 2
def baseEnd_452138 : Nat := 77388038720885747231887

theorem tailTrace_452138 : CollatzResearch.WordTrace tailWord_452138 prefixEnd_452138 77388038720885747231887 := by
  unfold tailWord_452138
  simp only [CollatzResearch.WordTrace]
  refine ⟨4122706908997179966947267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10993885090659146578526045 4122706908997179966947267)
  ·
    refine ⟨6184060363495769950420901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4122706908997179966947267 6184060363495769950420901)
    ·
      refine ⟨1159511318155456865703919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6184060363495769950420901 1159511318155456865703919)
      ·
        refine ⟨1739266977233185298555879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1159511318155456865703919 1739266977233185298555879)
        ·
          refine ⟨2608900465849777947833819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1739266977233185298555879 2608900465849777947833819)
          ·
            refine ⟨3913350698774666921750729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2608900465849777947833819 3913350698774666921750729)
            ·
              refine ⟨2935013024081000191313047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3913350698774666921750729 2935013024081000191313047)
              ·
                refine ⟨4402519536121500286969571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2935013024081000191313047 4402519536121500286969571)
                ·
                  refine ⟨6603779304182250430454357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4402519536121500286969571 6603779304182250430454357)
                  ·
                    refine ⟨77388038720885747231887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 6603779304182250430454357 77388038720885747231887)
                    ·
                      rfl

theorem cell23_452138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_452138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_452138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_452138 prefixEnd_452138 := by exact prefixLift 452138
  have htrace : WordTrace (prefixWord ++ tailWord_452138) baseStart_452138 baseEnd_452138 := by
    simpa [prefixWord, tailWord_452138, baseEnd_452138] using wordTrace_append hprefix tailTrace_452138
  have hstable : (prefixWord ++ tailWord_452138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452138).length < 2 ^ (prefixWord ++ tailWord_452138).sum := by decide
  have hdescent : baseEnd_452138 < baseStart_452138 := by decide
  rcases family_descends (prefixWord ++ tailWord_452138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452145 : List Nat := [1, 2, 2, 3, 1, 1, 1, 5, 1, 4, 2]
def baseStart_452145 : Nat := 118140960795 + 452145 * 2 ^ 59
def prefixEnd_452145 : Nat := 4983230072969 + 3 ^ 40 * 452145 * 2
def baseEnd_452145 : Nat := 232167710527238714308129

theorem tailTrace_452145 : CollatzResearch.WordTrace tailWord_452145 prefixEnd_452145 232167710527238714308129 := by
  unfold tailWord_452145
  simp only [CollatzResearch.WordTrace]
  refine ⟨16491082946963360063293889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10994055297975573375529259 16491082946963360063293889)
  ·
    refine ⟨12368312210222520047470417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16491082946963360063293889 12368312210222520047470417)
    ·
      refine ⟨9276234157666890035602813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12368312210222520047470417 9276234157666890035602813)
      ·
        refine ⟨3478587809125083763351055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9276234157666890035602813 3478587809125083763351055)
        ·
          refine ⟨5217881713687625645026583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3478587809125083763351055 5217881713687625645026583)
          ·
            refine ⟨7826822570531438467539875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5217881713687625645026583 7826822570531438467539875)
            ·
              refine ⟨11740233855797157701309813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7826822570531438467539875 11740233855797157701309813)
              ·
                refine ⟨1100646923980983534497795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11740233855797157701309813 1100646923980983534497795)
                ·
                  refine ⟨1650970385971475301746693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1100646923980983534497795 1650970385971475301746693)
                  ·
                    refine ⟨309556947369651619077505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1650970385971475301746693 309556947369651619077505)
                    ·
                      refine ⟨232167710527238714308129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 309556947369651619077505 232167710527238714308129)
                      ·
                        rfl

theorem cell23_452145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 4, 2].length) (baseStart_452145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_452145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_452145 prefixEnd_452145 := by exact prefixLift 452145
  have htrace : WordTrace (prefixWord ++ tailWord_452145) baseStart_452145 baseEnd_452145 := by
    simpa [prefixWord, tailWord_452145, baseEnd_452145] using wordTrace_append hprefix tailTrace_452145
  have hstable : (prefixWord ++ tailWord_452145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452145).length < 2 ^ (prefixWord ++ tailWord_452145).sum := by decide
  have hdescent : baseEnd_452145 < baseStart_452145 := by decide
  rcases family_descends (prefixWord ++ tailWord_452145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452149 : List Nat := [1, 3, 3, 1, 1, 5, 1, 2, 1, 3, 2]
def baseStart_452149 : Nat := 118140960795 + 452149 * 2 ^ 59
def prefixEnd_452149 : Nat := 4983230072969 + 3 ^ 40 * 452149 * 2
def baseEnd_452149 : Nat := 232169764449856698658111

theorem tailTrace_452149 : CollatzResearch.WordTrace tailWord_452149 prefixEnd_452149 232169764449856698658111 := by
  unfold tailWord_452149
  simp only [CollatzResearch.WordTrace]
  refine ⟨16491228838948868746439501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10994152559299245830959667 16491228838948868746439501)
  ·
    refine ⟨6184210814605825779914813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16491228838948868746439501 6184210814605825779914813)
    ·
      refine ⟨2319079055477184667468055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6184210814605825779914813 2319079055477184667468055)
      ·
        refine ⟨3478618583215777001202083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2319079055477184667468055 3478618583215777001202083)
        ·
          refine ⟨5217927874823665501803125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3478618583215777001202083 5217927874823665501803125)
          ·
            refine ⟨489180738264718640794043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5217927874823665501803125 489180738264718640794043)
            ·
              refine ⟨733771107397077961191065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 489180738264718640794043 733771107397077961191065)
              ·
                refine ⟨550328330547808470893299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 733771107397077961191065 550328330547808470893299)
                ·
                  refine ⟨825492495821712706339949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 550328330547808470893299 825492495821712706339949)
                  ·
                    refine ⟨309559685933142264877481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 825492495821712706339949 309559685933142264877481)
                    ·
                      refine ⟨232169764449856698658111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 309559685933142264877481 232169764449856698658111)
                      ·
                        rfl

theorem cell23_452149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 2, 1, 3, 2].length) (baseStart_452149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_452149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_452149 prefixEnd_452149 := by exact prefixLift 452149
  have htrace : WordTrace (prefixWord ++ tailWord_452149) baseStart_452149 baseEnd_452149 := by
    simpa [prefixWord, tailWord_452149, baseEnd_452149] using wordTrace_append hprefix tailTrace_452149
  have hstable : (prefixWord ++ tailWord_452149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452149).length < 2 ^ (prefixWord ++ tailWord_452149).sum := by decide
  have hdescent : baseEnd_452149 < baseStart_452149 := by decide
  rcases family_descends (prefixWord ++ tailWord_452149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452195 : List Nat := [1, 1, 1, 5, 1, 4, 1, 1, 2, 3, 3]
def baseStart_452195 : Nat := 118140960795 + 452195 * 2 ^ 59
def prefixEnd_452195 : Nat := 4983230072969 + 3 ^ 40 * 452195 * 2
def baseEnd_452195 : Nat := 232193384559963518682899

theorem tailTrace_452195 : CollatzResearch.WordTrace tailWord_452195 prefixEnd_452195 232193384559963518682899 := by
  unfold tailWord_452195
  simp only [CollatzResearch.WordTrace]
  refine ⟨16492906596782218602614039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10995271064521479068409359 16492906596782218602614039)
  ·
    refine ⟨24739359895173327903921059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16492906596782218602614039 24739359895173327903921059)
    ·
      refine ⟨37109039842759991855881589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24739359895173327903921059 37109039842759991855881589)
      ·
        refine ⟨3478972485258749236488899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37109039842759991855881589 3478972485258749236488899)
        ·
          refine ⟨5218458727888123854733349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3478972485258749236488899 5218458727888123854733349)
          ·
            refine ⟨978461011479023222762503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5218458727888123854733349 978461011479023222762503)
            ·
              refine ⟨1467691517218534834143755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 978461011479023222762503 1467691517218534834143755)
              ·
                refine ⟨2201537275827802251215633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1467691517218534834143755 2201537275827802251215633)
                ·
                  refine ⟨1651152956870851688411725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2201537275827802251215633 1651152956870851688411725)
                  ·
                    refine ⟨619182358826569383154397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1651152956870851688411725 619182358826569383154397)
                    ·
                      refine ⟨232193384559963518682899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 619182358826569383154397 232193384559963518682899)
                      ·
                        rfl

theorem cell23_452195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_452195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_452195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_452195 prefixEnd_452195 := by exact prefixLift 452195
  have htrace : WordTrace (prefixWord ++ tailWord_452195) baseStart_452195 baseEnd_452195 := by
    simpa [prefixWord, tailWord_452195, baseEnd_452195] using wordTrace_append hprefix tailTrace_452195
  have hstable : (prefixWord ++ tailWord_452195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452195).length < 2 ^ (prefixWord ++ tailWord_452195).sum := by decide
  have hdescent : baseEnd_452195 < baseStart_452195 := by decide
  rcases family_descends (prefixWord ++ tailWord_452195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452235 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 4, 4, 2]
def baseStart_452235 : Nat := 118140960795 + 452235 * 2 ^ 59
def prefixEnd_452235 : Nat := 4983230072969 + 3 ^ 40 * 452235 * 2
def baseEnd_452235 : Nat := 232213923786143362182715

theorem tailTrace_452235 : CollatzResearch.WordTrace tailWord_452235 prefixEnd_452235 232213923786143362182715 := by
  unfold tailWord_452235
  simp only [CollatzResearch.WordTrace]
  refine ⟨16494365516637305434070159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10996243677758203622713439 16494365516637305434070159)
  ·
    refine ⟨24741548274955958151105239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16494365516637305434070159 24741548274955958151105239)
    ·
      refine ⟨37112322412433937226657859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24741548274955958151105239 37112322412433937226657859)
      ·
        refine ⟨55668483618650905839986789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37112322412433937226657859 55668483618650905839986789)
        ·
          refine ⟨10437840678497044844997523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55668483618650905839986789 10437840678497044844997523)
          ·
            refine ⟨15656761017745567267496285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10437840678497044844997523 15656761017745567267496285)
            ·
              refine ⟨5871285381654587725311107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15656761017745567267496285 5871285381654587725311107)
              ·
                refine ⟨8806928072481881587966661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5871285381654587725311107 8806928072481881587966661)
                ·
                  refine ⟨1651299013590352797743749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8806928072481881587966661 1651299013590352797743749)
                  ·
                    refine ⟨309618565048191149576953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1651299013590352797743749 309618565048191149576953)
                    ·
                      refine ⟨232213923786143362182715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 309618565048191149576953 232213923786143362182715)
                      ·
                        rfl

theorem cell23_452235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 4, 2].length) (baseStart_452235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_452235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_452235 prefixEnd_452235 := by exact prefixLift 452235
  have htrace : WordTrace (prefixWord ++ tailWord_452235) baseStart_452235 baseEnd_452235 := by
    simpa [prefixWord, tailWord_452235, baseEnd_452235] using wordTrace_append hprefix tailTrace_452235
  have hstable : (prefixWord ++ tailWord_452235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452235).length < 2 ^ (prefixWord ++ tailWord_452235).sum := by decide
  have hdescent : baseEnd_452235 < baseStart_452235 := by decide
  rcases family_descends (prefixWord ++ tailWord_452235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452279 : List Nat := [1, 1, 3, 1, 5, 1, 3, 3, 1, 4]
def baseStart_452279 : Nat := 118140960795 + 452279 * 2 ^ 59
def prefixEnd_452279 : Nat := 4983230072969 + 3 ^ 40 * 452279 * 2
def baseEnd_452279 : Nat := 77412172311647063344171

theorem tailTrace_452279 : CollatzResearch.WordTrace tailWord_452279 prefixEnd_452279 77412172311647063344171 := by
  unfold tailWord_452279
  simp only [CollatzResearch.WordTrace]
  refine ⟨16495970328477900948671891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10997313552318600632447927 16495970328477900948671891)
  ·
    refine ⟨24743955492716851423007837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16495970328477900948671891 24743955492716851423007837)
    ·
      refine ⟨9278983309768819283627939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24743955492716851423007837 9278983309768819283627939)
      ·
        refine ⟨13918474964653228925441909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9278983309768819283627939 13918474964653228925441909)
        ·
          refine ⟨1304857027936240211760179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13918474964653228925441909 1304857027936240211760179)
          ·
            refine ⟨1957285541904360317640269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1304857027936240211760179 1957285541904360317640269)
            ·
              refine ⟨733982078214135119115101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1957285541904360317640269 733982078214135119115101)
              ·
                refine ⟨275243279330300669668163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 733982078214135119115101 275243279330300669668163)
                ·
                  refine ⟨412864918995451004502245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 275243279330300669668163 412864918995451004502245)
                  ·
                    refine ⟨77412172311647063344171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 412864918995451004502245 77412172311647063344171)
                    ·
                      rfl

theorem cell23_452279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 3, 1, 4].length) (baseStart_452279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_452279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_452279 prefixEnd_452279 := by exact prefixLift 452279
  have htrace : WordTrace (prefixWord ++ tailWord_452279) baseStart_452279 baseEnd_452279 := by
    simpa [prefixWord, tailWord_452279, baseEnd_452279] using wordTrace_append hprefix tailTrace_452279
  have hstable : (prefixWord ++ tailWord_452279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452279).length < 2 ^ (prefixWord ++ tailWord_452279).sum := by decide
  have hdescent : baseEnd_452279 < baseStart_452279 := by decide
  rcases family_descends (prefixWord ++ tailWord_452279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452312 : List Nat := [2, 1, 2, 2, 3, 1, 1, 2, 4, 3, 2]
def baseStart_452312 : Nat := 118140960795 + 452312 * 2 ^ 59
def prefixEnd_452312 : Nat := 4983230072969 + 3 ^ 40 * 452312 * 2
def baseEnd_452312 : Nat := 232253461796539560919861

theorem tailTrace_452312 : CollatzResearch.WordTrace tailWord_452312 prefixEnd_452312 232253461796539560919861 := by
  unfold tailWord_452312
  simp only [CollatzResearch.WordTrace]
  refine ⟨8248586968679173792311595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10998115958238898389748793 8248586968679173792311595)
  ·
    refine ⟨12372880453018760688467393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8248586968679173792311595 12372880453018760688467393)
    ·
      refine ⟨9279660339764070516350545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12372880453018760688467393 9279660339764070516350545)
      ·
        refine ⟨6959745254823052887262909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9279660339764070516350545 6959745254823052887262909)
        ·
          refine ⟨2609904470558644832723591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6959745254823052887262909 2609904470558644832723591)
          ·
            refine ⟨3914856705837967249085387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2609904470558644832723591 3914856705837967249085387)
            ·
              refine ⟨5872285058756950873628081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3914856705837967249085387 5872285058756950873628081)
              ·
                refine ⟨4404213794067713155221061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5872285058756950873628081 4404213794067713155221061)
                ·
                  refine ⟨825790086387696216603949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4404213794067713155221061 825790086387696216603949)
                  ·
                    refine ⟨309671282395386081226481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 825790086387696216603949 309671282395386081226481)
                    ·
                      refine ⟨232253461796539560919861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 309671282395386081226481 232253461796539560919861)
                      ·
                        rfl

theorem cell23_452312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 4, 3, 2].length) (baseStart_452312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_452312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_452312 prefixEnd_452312 := by exact prefixLift 452312
  have htrace : WordTrace (prefixWord ++ tailWord_452312) baseStart_452312 baseEnd_452312 := by
    simpa [prefixWord, tailWord_452312, baseEnd_452312] using wordTrace_append hprefix tailTrace_452312
  have hstable : (prefixWord ++ tailWord_452312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452312).length < 2 ^ (prefixWord ++ tailWord_452312).sum := by decide
  have hdescent : baseEnd_452312 < baseStart_452312 := by decide
  rcases family_descends (prefixWord ++ tailWord_452312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452335 : List Nat := [1, 1, 2, 1, 5, 1, 3, 2, 1, 6]
def baseStart_452335 : Nat := 118140960795 + 452335 * 2 ^ 59
def prefixEnd_452335 : Nat := 4983230072969 + 3 ^ 40 * 452335 * 2
def baseEnd_452335 : Nat := 77421757283864323644085

theorem tailTrace_452335 : CollatzResearch.WordTrace tailWord_452335 prefixEnd_452335 77421757283864323644085 := by
  unfold tailWord_452335
  simp only [CollatzResearch.WordTrace]
  refine ⟨16498012816275022512710459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10998675210850015008473639 16498012816275022512710459)
  ·
    refine ⟨24747019224412533769065689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16498012816275022512710459 24747019224412533769065689)
    ·
      refine ⟨18560264418309400326799267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24747019224412533769065689 18560264418309400326799267)
      ·
        refine ⟨27840396627464100490198901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18560264418309400326799267 27840396627464100490198901)
        ·
          refine ⟨2610037183824759420956147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27840396627464100490198901 2610037183824759420956147)
          ·
            refine ⟨3915055775737139131434221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2610037183824759420956147 3915055775737139131434221)
            ·
              refine ⟨1468145915901427174287833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3915055775737139131434221 1468145915901427174287833)
              ·
                refine ⟨1101109436926070380715875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1468145915901427174287833 1101109436926070380715875)
                ·
                  refine ⟨1651664155389105571073813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1101109436926070380715875 1651664155389105571073813)
                  ·
                    refine ⟨77421757283864323644085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1651664155389105571073813 77421757283864323644085)
                    ·
                      rfl

theorem cell23_452335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 6].length) (baseStart_452335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_452335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_452335 prefixEnd_452335 := by exact prefixLift 452335
  have htrace : WordTrace (prefixWord ++ tailWord_452335) baseStart_452335 baseEnd_452335 := by
    simpa [prefixWord, tailWord_452335, baseEnd_452335] using wordTrace_append hprefix tailTrace_452335
  have hstable : (prefixWord ++ tailWord_452335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452335).length < 2 ^ (prefixWord ++ tailWord_452335).sum := by decide
  have hdescent : baseEnd_452335 < baseStart_452335 := by decide
  rcases family_descends (prefixWord ++ tailWord_452335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452362 : List Nat := [3, 1, 2, 2, 1, 3, 1, 2, 3, 2, 3]
def baseStart_452362 : Nat := 118140960795 + 452362 * 2 ^ 59
def prefixEnd_452362 : Nat := 4983230072969 + 3 ^ 40 * 452362 * 2
def baseEnd_452362 : Nat := 232279135829264365294631

theorem tailTrace_452362 : CollatzResearch.WordTrace tailWord_452362 prefixEnd_452362 232279135829264365294631 := by
  unfold tailWord_452362
  simp only [CollatzResearch.WordTrace]
  refine ⟨4124749396794301530985835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10999331724784804082628893 4124749396794301530985835)
  ·
    refine ⟨6187124095191452296478753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4124749396794301530985835 6187124095191452296478753)
    ·
      refine ⟨4640343071393589222359065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6187124095191452296478753 4640343071393589222359065)
      ·
        refine ⟨3480257303545191916769299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4640343071393589222359065 3480257303545191916769299)
        ·
          refine ⟨5220385955317787875153949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3480257303545191916769299 5220385955317787875153949)
          ·
            refine ⟨1957644733244170453182731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5220385955317787875153949 1957644733244170453182731)
            ·
              refine ⟨2936467099866255679774097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1957644733244170453182731 2936467099866255679774097)
              ·
                refine ⟨2202350324899691759830573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2936467099866255679774097 2202350324899691759830573)
                ·
                  refine ⟨825881371837384409936465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2202350324899691759830573 825881371837384409936465)
                  ·
                    refine ⟨619411028878038307452349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 825881371837384409936465 619411028878038307452349)
                    ·
                      refine ⟨232279135829264365294631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 619411028878038307452349 232279135829264365294631)
                      ·
                        rfl

theorem cell23_452362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_452362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_452362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_452362 prefixEnd_452362 := by exact prefixLift 452362
  have htrace : WordTrace (prefixWord ++ tailWord_452362) baseStart_452362 baseEnd_452362 := by
    simpa [prefixWord, tailWord_452362, baseEnd_452362] using wordTrace_append hprefix tailTrace_452362
  have hstable : (prefixWord ++ tailWord_452362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452362).length < 2 ^ (prefixWord ++ tailWord_452362).sum := by decide
  have hdescent : baseEnd_452362 < baseStart_452362 := by decide
  rcases family_descends (prefixWord ++ tailWord_452362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452396 : List Nat := [2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 3]
def baseStart_452396 : Nat := 118140960795 + 452396 * 2 ^ 59
def prefixEnd_452396 : Nat := 4983230072969 + 3 ^ 40 * 452396 * 2
def baseEnd_452396 : Nat := 232296594171517232269475

theorem tailTrace_452396 : CollatzResearch.WordTrace tailWord_452396 prefixEnd_452396 232296594171517232269475 := by
  unfold tailWord_452396
  simp only [CollatzResearch.WordTrace]
  refine ⟨8250118834527014965340521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11000158446036019953787361 8250118834527014965340521)
  ·
    refine ⟨6187589125895261224005391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8250118834527014965340521 6187589125895261224005391)
    ·
      refine ⟨9281383688842891836008087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6187589125895261224005391 9281383688842891836008087)
      ·
        refine ⟨13922075533264337754012131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9281383688842891836008087 13922075533264337754012131)
        ·
          refine ⟨20883113299896506631018197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13922075533264337754012131 20883113299896506631018197)
          ·
            refine ⟨489447967966324374164489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 20883113299896506631018197 489447967966324374164489)
            ·
              refine ⟨367085975974743280623367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 489447967966324374164489 367085975974743280623367)
              ·
                refine ⟨550628963962114920935051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367085975974743280623367 550628963962114920935051)
                ·
                  refine ⟨825943445943172381402577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 550628963962114920935051 825943445943172381402577)
                  ·
                    refine ⟨619457584457379286051933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 825943445943172381402577 619457584457379286051933)
                    ·
                      refine ⟨232296594171517232269475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 619457584457379286051933 232296594171517232269475)
                      ·
                        rfl

theorem cell23_452396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 3].length) (baseStart_452396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_452396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_452396 prefixEnd_452396 := by exact prefixLift 452396
  have htrace : WordTrace (prefixWord ++ tailWord_452396) baseStart_452396 baseEnd_452396 := by
    simpa [prefixWord, tailWord_452396, baseEnd_452396] using wordTrace_append hprefix tailTrace_452396
  have hstable : (prefixWord ++ tailWord_452396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452396).length < 2 ^ (prefixWord ++ tailWord_452396).sum := by decide
  have hdescent : baseEnd_452396 < baseStart_452396 := by decide
  rcases family_descends (prefixWord ++ tailWord_452396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452425 : List Nat := [1, 2, 1, 1, 2, 4, 1, 3, 2, 6]
def baseStart_452425 : Nat := 118140960795 + 452425 * 2 ^ 59
def prefixEnd_452425 : Nat := 4983230072969 + 3 ^ 40 * 452425 * 2
def baseEnd_452425 : Nat := 77437161703499206268947

theorem tailTrace_452425 : CollatzResearch.WordTrace tailWord_452425 prefixEnd_452425 77437161703499206268947 := by
  unfold tailWord_452425
  simp only [CollatzResearch.WordTrace]
  refine ⟨16501295385948967883486729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11000863590632645255657819 16501295385948967883486729)
  ·
    refine ⟨12375971539461725912615047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16501295385948967883486729 12375971539461725912615047)
    ·
      refine ⟨18563957309192588868922571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12375971539461725912615047 18563957309192588868922571)
      ·
        refine ⟨27845935963788883303383857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18563957309192588868922571 27845935963788883303383857)
        ·
          refine ⟨20884451972841662477537893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27845935963788883303383857 20884451972841662477537893)
          ·
            refine ⟨3915834744907811714538355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20884451972841662477537893 3915834744907811714538355)
            ·
              refine ⟨5873752117361717571807533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3915834744907811714538355 5873752117361717571807533)
              ·
                refine ⟨2202657044010644089427825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5873752117361717571807533 2202657044010644089427825)
                ·
                  refine ⟨1651992783007983067070869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2202657044010644089427825 1651992783007983067070869)
                  ·
                    refine ⟨77437161703499206268947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1651992783007983067070869 77437161703499206268947)
                    ·
                      rfl

theorem cell23_452425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 6].length) (baseStart_452425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_452425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_452425 prefixEnd_452425 := by exact prefixLift 452425
  have htrace : WordTrace (prefixWord ++ tailWord_452425) baseStart_452425 baseEnd_452425 := by
    simpa [prefixWord, tailWord_452425, baseEnd_452425] using wordTrace_append hprefix tailTrace_452425
  have hstable : (prefixWord ++ tailWord_452425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452425).length < 2 ^ (prefixWord ++ tailWord_452425).sum := by decide
  have hdescent : baseEnd_452425 < baseStart_452425 := by decide
  rcases family_descends (prefixWord ++ tailWord_452425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452426 : List Nat := [3, 1, 2, 1, 1, 1, 7, 1, 2, 1, 3]
def baseStart_452426 : Nat := 118140960795 + 452426 * 2 ^ 59
def prefixEnd_452426 : Nat := 4983230072969 + 3 ^ 40 * 452426 * 2
def baseEnd_452426 : Nat := 232311998591152114894337

theorem tailTrace_452426 : CollatzResearch.WordTrace tailWord_452426 prefixEnd_452426 232311998591152114894337 := by
  unfold tailWord_452426
  simp only [CollatzResearch.WordTrace]
  refine ⟨4125332964736336263568283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11000887905963563369515421 4125332964736336263568283)
  ·
    refine ⟨6187999447104504395352425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4125332964736336263568283 6187999447104504395352425)
    ·
      refine ⟨4640999585328378296514319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6187999447104504395352425 4640999585328378296514319)
      ·
        refine ⟨6961499377992567444771479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4640999585328378296514319 6961499377992567444771479)
        ·
          refine ⟨10442249066988851167157219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6961499377992567444771479 10442249066988851167157219)
          ·
            refine ⟨15663373600483276750735829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10442249066988851167157219 15663373600483276750735829)
            ·
              refine ⟨367110318761326798845371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 15663373600483276750735829 367110318761326798845371)
              ·
                refine ⟨550665478141990198268057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367110318761326798845371 550665478141990198268057)
                ·
                  refine ⟨412999108606492648701043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 550665478141990198268057 412999108606492648701043)
                  ·
                    refine ⟨619498662909738973051565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 412999108606492648701043 619498662909738973051565)
                    ·
                      refine ⟨232311998591152114894337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 619498662909738973051565 232311998591152114894337)
                      ·
                        rfl

theorem cell23_452426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 1, 2, 1, 3].length) (baseStart_452426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_452426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_452426 prefixEnd_452426 := by exact prefixLift 452426
  have htrace : WordTrace (prefixWord ++ tailWord_452426) baseStart_452426 baseEnd_452426 := by
    simpa [prefixWord, tailWord_452426, baseEnd_452426] using wordTrace_append hprefix tailTrace_452426
  have hstable : (prefixWord ++ tailWord_452426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452426).length < 2 ^ (prefixWord ++ tailWord_452426).sum := by decide
  have hdescent : baseEnd_452426 < baseStart_452426 := by decide
  rcases family_descends (prefixWord ++ tailWord_452426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452436 : List Nat := [2, 4, 1, 1, 3, 1, 1, 4, 1, 3, 2]
def baseStart_452436 : Nat := 118140960795 + 452436 * 2 ^ 59
def prefixEnd_452436 : Nat := 4983230072969 + 3 ^ 40 * 452436 * 2
def baseEnd_452436 : Nat := 232317133397697075769291

theorem tailTrace_452436 : CollatzResearch.WordTrace tailWord_452436 prefixEnd_452436 232317133397697075769291 := by
  unfold tailWord_452436
  simp only [CollatzResearch.WordTrace]
  refine ⟨8250848294454558381068581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11001131059272744508091441 8250848294454558381068581)
  ·
    refine ⟨1547034055210229696450359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8250848294454558381068581 1547034055210229696450359)
    ·
      refine ⟨2320551082815344544675539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1547034055210229696450359 2320551082815344544675539)
      ·
        refine ⟨3480826624223016817013309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2320551082815344544675539 3480826624223016817013309)
        ·
          refine ⟨1305309984083631306379991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3480826624223016817013309 1305309984083631306379991)
          ·
            refine ⟨1957964976125446959569987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1305309984083631306379991 1957964976125446959569987)
            ·
              refine ⟨2936947464188170439354981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1957964976125446959569987 2936947464188170439354981)
              ·
                refine ⟨550677649535281957379059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2936947464188170439354981 550677649535281957379059)
                ·
                  refine ⟨826016474302922936068589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 550677649535281957379059 826016474302922936068589)
                  ·
                    refine ⟨309756177863596101025721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 826016474302922936068589 309756177863596101025721)
                    ·
                      refine ⟨232317133397697075769291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 309756177863596101025721 232317133397697075769291)
                      ·
                        rfl

theorem cell23_452436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 4, 1, 3, 2].length) (baseStart_452436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_452436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_452436 prefixEnd_452436 := by exact prefixLift 452436
  have htrace : WordTrace (prefixWord ++ tailWord_452436) baseStart_452436 baseEnd_452436 := by
    simpa [prefixWord, tailWord_452436, baseEnd_452436] using wordTrace_append hprefix tailTrace_452436
  have hstable : (prefixWord ++ tailWord_452436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452436).length < 2 ^ (prefixWord ++ tailWord_452436).sum := by decide
  have hdescent : baseEnd_452436 < baseStart_452436 := by decide
  rcases family_descends (prefixWord ++ tailWord_452436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452449 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 6, 2, 2]
def baseStart_452449 : Nat := 118140960795 + 452449 * 2 ^ 59
def prefixEnd_452449 : Nat := 4983230072969 + 3 ^ 40 * 452449 * 2
def baseEnd_452449 : Nat := 232323808646205524906731

theorem tailTrace_452449 : CollatzResearch.WordTrace tailWord_452449 prefixEnd_452449 232323808646205524906731 := by
  unfold tailWord_452449
  simp only [CollatzResearch.WordTrace]
  refine ⟨16502170737862019982360401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11001447158574679988240267 16502170737862019982360401)
  ·
    refine ⟨12376628053396514986770301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16502170737862019982360401 12376628053396514986770301)
    ·
      refine ⟨4641235520023693120038863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12376628053396514986770301 4641235520023693120038863)
      ·
        refine ⟨6961853280035539680058295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4641235520023693120038863 6961853280035539680058295)
        ·
          refine ⟨10442779920053309520087443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6961853280035539680058295 10442779920053309520087443)
          ·
            refine ⟨15664169880079964280131165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10442779920053309520087443 15664169880079964280131165)
            ·
              refine ⟨5874063705029986605049187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15664169880079964280131165 5874063705029986605049187)
              ·
                refine ⟨8811095557544979907573781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5874063705029986605049187 8811095557544979907573781)
                ·
                  refine ⟨413020104259920933167521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8811095557544979907573781 413020104259920933167521)
                  ·
                    refine ⟨309765078194940699875641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 413020104259920933167521 309765078194940699875641)
                    ·
                      refine ⟨232323808646205524906731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 309765078194940699875641 232323808646205524906731)
                      ·
                        rfl

theorem cell23_452449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 6, 2, 2].length) (baseStart_452449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_452449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_452449 prefixEnd_452449 := by exact prefixLift 452449
  have htrace : WordTrace (prefixWord ++ tailWord_452449) baseStart_452449 baseEnd_452449 := by
    simpa [prefixWord, tailWord_452449, baseEnd_452449] using wordTrace_append hprefix tailTrace_452449
  have hstable : (prefixWord ++ tailWord_452449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452449).length < 2 ^ (prefixWord ++ tailWord_452449).sum := by decide
  have hdescent : baseEnd_452449 < baseStart_452449 := by decide
  rcases family_descends (prefixWord ++ tailWord_452449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452465 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 1, 2, 7]
def baseStart_452465 : Nat := 118140960795 + 452465 * 2 ^ 59
def prefixEnd_452465 : Nat := 4983230072969 + 3 ^ 40 * 452465 * 2
def baseEnd_452465 : Nat := 232332024336677462306657

theorem tailTrace_452465 : CollatzResearch.WordTrace tailWord_452465 prefixEnd_452465 232332024336677462306657 := by
  unfold tailWord_452465
  simp only [CollatzResearch.WordTrace]
  refine ⟨16502754305804054714942849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11001836203869369809961899 16502754305804054714942849)
  ·
    refine ⟨12377065729353041036207137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16502754305804054714942849 12377065729353041036207137)
    ·
      refine ⟨9282799297014780777155353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12377065729353041036207137 9282799297014780777155353)
      ·
        refine ⟨6962099472761085582866515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9282799297014780777155353 6962099472761085582866515)
        ·
          refine ⟨10443149209141628374299773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6962099472761085582866515 10443149209141628374299773)
          ·
            refine ⟨3916180953428110640362415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10443149209141628374299773 3916180953428110640362415)
            ·
              refine ⟨5874271430142165960543623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3916180953428110640362415 5874271430142165960543623)
              ·
                refine ⟨8811407145213248940815435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5874271430142165960543623 8811407145213248940815435)
                ·
                  refine ⟨13217110717819873411223153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8811407145213248940815435 13217110717819873411223153)
                  ·
                    refine ⟨9912833038364905058417365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13217110717819873411223153 9912833038364905058417365)
                    ·
                      refine ⟨232332024336677462306657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 9912833038364905058417365 232332024336677462306657)
                      ·
                        rfl

theorem cell23_452465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_452465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_452465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_452465 prefixEnd_452465 := by exact prefixLift 452465
  have htrace : WordTrace (prefixWord ++ tailWord_452465) baseStart_452465 baseEnd_452465 := by
    simpa [prefixWord, tailWord_452465, baseEnd_452465] using wordTrace_append hprefix tailTrace_452465
  have hstable : (prefixWord ++ tailWord_452465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452465).length < 2 ^ (prefixWord ++ tailWord_452465).sum := by decide
  have hdescent : baseEnd_452465 < baseStart_452465 := by decide
  rcases family_descends (prefixWord ++ tailWord_452465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452466 : List Nat := [3, 2, 1, 2, 1, 1, 1, 6, 2, 2, 2]
def baseStart_452466 : Nat := 118140960795 + 452466 * 2 ^ 59
def prefixEnd_452466 : Nat := 4983230072969 + 3 ^ 40 * 452466 * 2
def baseEnd_452466 : Nat := 232332537817331958394153

theorem tailTrace_452466 : CollatzResearch.WordTrace tailWord_452466 prefixEnd_452466 232332537817331958394153 := by
  unfold tailWord_452466
  simp only [CollatzResearch.WordTrace]
  refine ⟨4125697694700107971432313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11001860519200287923819501 4125697694700107971432313)
  ·
    refine ⟨3094273271025080978574235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4125697694700107971432313 3094273271025080978574235)
    ·
      refine ⟨4641409906537621467861353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3094273271025080978574235 4641409906537621467861353)
      ·
        refine ⟨3481057429903216100896015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4641409906537621467861353 3481057429903216100896015)
        ·
          refine ⟨5221586144854824151344023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3481057429903216100896015 5221586144854824151344023)
          ·
            refine ⟨7832379217282236227016035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5221586144854824151344023 7832379217282236227016035)
            ·
              refine ⟨11748568825923354340524053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7832379217282236227016035 11748568825923354340524053)
              ·
                refine ⟨550714163715157234712065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11748568825923354340524053 550714163715157234712065)
                ·
                  refine ⟨413035622786367926034049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 550714163715157234712065 413035622786367926034049)
                  ·
                    refine ⟨309776717089775944525537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 413035622786367926034049 309776717089775944525537)
                    ·
                      refine ⟨232332537817331958394153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 309776717089775944525537 232332537817331958394153)
                      ·
                        rfl

theorem cell23_452466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 6, 2, 2, 2].length) (baseStart_452466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_452466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_452466 prefixEnd_452466 := by exact prefixLift 452466
  have htrace : WordTrace (prefixWord ++ tailWord_452466) baseStart_452466 baseEnd_452466 := by
    simpa [prefixWord, tailWord_452466, baseEnd_452466] using wordTrace_append hprefix tailTrace_452466
  have hstable : (prefixWord ++ tailWord_452466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452466).length < 2 ^ (prefixWord ++ tailWord_452466).sum := by decide
  have hdescent : baseEnd_452466 < baseStart_452466 := by decide
  rcases family_descends (prefixWord ++ tailWord_452466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452483 : List Nat := [1, 1, 1, 3, 4, 2, 4, 1, 2, 2, 2]
def baseStart_452483 : Nat := 118140960795 + 452483 * 2 ^ 59
def prefixEnd_452483 : Nat := 4983230072969 + 3 ^ 40 * 452483 * 2
def baseEnd_452483 : Nat := 232341266988458391881575

theorem tailTrace_452483 : CollatzResearch.WordTrace tailWord_452483 prefixEnd_452483 232341266988458391881575 := by
  unfold tailWord_452483
  simp only [CollatzResearch.WordTrace]
  refine ⟨16503410819738843789098103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11002273879825895859398735 16503410819738843789098103)
  ·
    refine ⟨24755116229608265683647155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16503410819738843789098103 24755116229608265683647155)
    ·
      refine ⟨37132674344412398525470733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24755116229608265683647155 37132674344412398525470733)
      ·
        refine ⟨13924752879154649447051525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37132674344412398525470733 13924752879154649447051525)
        ·
          refine ⟨2610891164841496771322161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13924752879154649447051525 2610891164841496771322161)
          ·
            refine ⟨1958168373631122578491621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2610891164841496771322161 1958168373631122578491621)
            ·
              refine ⟨367156570055835483467179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1958168373631122578491621 367156570055835483467179)
              ·
                refine ⟨550734855083753225200769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367156570055835483467179 550734855083753225200769)
                ·
                  refine ⟨413051141312814918900577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 550734855083753225200769 413051141312814918900577)
                  ·
                    refine ⟨309788355984611189175433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 413051141312814918900577 309788355984611189175433)
                    ·
                      refine ⟨232341266988458391881575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 309788355984611189175433 232341266988458391881575)
                      ·
                        rfl

theorem cell23_452483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 1, 2, 2, 2].length) (baseStart_452483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_452483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_452483 prefixEnd_452483 := by exact prefixLift 452483
  have htrace : WordTrace (prefixWord ++ tailWord_452483) baseStart_452483 baseEnd_452483 := by
    simpa [prefixWord, tailWord_452483, baseEnd_452483] using wordTrace_append hprefix tailTrace_452483
  have hstable : (prefixWord ++ tailWord_452483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452483).length < 2 ^ (prefixWord ++ tailWord_452483).sum := by decide
  have hdescent : baseEnd_452483 < baseStart_452483 := by decide
  rcases family_descends (prefixWord ++ tailWord_452483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452519 : List Nat := [1, 1, 6, 1, 2, 1, 2, 2, 2, 5]
def baseStart_452519 : Nat := 118140960795 + 452519 * 2 ^ 59
def prefixEnd_452519 : Nat := 4983230072969 + 3 ^ 40 * 452519 * 2
def baseEnd_452519 : Nat := 77453250764006750343803

theorem tailTrace_452519 : CollatzResearch.WordTrace tailWord_452519 prefixEnd_452519 77453250764006750343803 := by
  unfold tailWord_452519
  simp only [CollatzResearch.WordTrace]
  refine ⟨16504723847608421937408611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11003149231738947958272407 16504723847608421937408611)
  ·
    refine ⟨24757085771412632906112917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16504723847608421937408611 24757085771412632906112917)
    ·
      refine ⟨1160488395534967167474043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24757085771412632906112917 1160488395534967167474043)
      ·
        refine ⟨1740732593302450751211065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1160488395534967167474043 1740732593302450751211065)
        ·
          refine ⟨1305549444976838063408299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1740732593302450751211065 1305549444976838063408299)
          ·
            refine ⟨1958324167465257095112449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1305549444976838063408299 1958324167465257095112449)
            ·
              refine ⟨1468743125598942821334337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1958324167465257095112449 1468743125598942821334337)
              ·
                refine ⟨1101557344199207116000753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1468743125598942821334337 1101557344199207116000753)
                ·
                  refine ⟨826168008149405337000565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1101557344199207116000753 826168008149405337000565)
                  ·
                    refine ⟨77453250764006750343803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 826168008149405337000565 77453250764006750343803)
                    ·
                      rfl

theorem cell23_452519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_452519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_452519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_452519 prefixEnd_452519 := by exact prefixLift 452519
  have htrace : WordTrace (prefixWord ++ tailWord_452519) baseStart_452519 baseEnd_452519 := by
    simpa [prefixWord, tailWord_452519, baseEnd_452519] using wordTrace_append hprefix tailTrace_452519
  have hstable : (prefixWord ++ tailWord_452519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452519).length < 2 ^ (prefixWord ++ tailWord_452519).sum := by decide
  have hdescent : baseEnd_452519 < baseStart_452519 := by decide
  rcases family_descends (prefixWord ++ tailWord_452519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452556 : List Nat := [2, 2, 1, 4, 1, 4, 1, 1, 2, 1, 4]
def baseStart_452556 : Nat := 118140960795 + 452556 * 2 ^ 59
def prefixEnd_452556 : Nat := 4983230072969 + 3 ^ 40 * 452556 * 2
def baseEnd_452556 : Nat := 232378751076236606268739

theorem tailTrace_452556 : CollatzResearch.WordTrace tailWord_452556 prefixEnd_452556 232378751076236606268739 := by
  unfold tailWord_452556
  simp only [CollatzResearch.WordTrace]
  refine ⟨8253036674237188628252761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11004048898982918171003681 8253036674237188628252761)
  ·
    refine ⟨6189777505677891471189571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8253036674237188628252761 6189777505677891471189571)
    ·
      refine ⟨9284666258516837206784357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6189777505677891471189571 9284666258516837206784357)
      ·
        refine ⟨1740874923471906976272067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9284666258516837206784357 1740874923471906976272067)
        ·
          refine ⟨2611312385207860464408101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1740874923471906976272067 2611312385207860464408101)
          ·
            refine ⟨489621072226473837076519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2611312385207860464408101 489621072226473837076519)
            ·
              refine ⟨734431608339710755614779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 489621072226473837076519 734431608339710755614779)
              ·
                refine ⟨1101647412509566133422169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 734431608339710755614779 1101647412509566133422169)
                ·
                  refine ⟨826235559382174600066627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1101647412509566133422169 826235559382174600066627)
                  ·
                    refine ⟨1239353339073261900099941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 826235559382174600066627 1239353339073261900099941)
                    ·
                      refine ⟨232378751076236606268739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1239353339073261900099941 232378751076236606268739)
                      ·
                        rfl

theorem cell23_452556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_452556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_452556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_452556 prefixEnd_452556 := by exact prefixLift 452556
  have htrace : WordTrace (prefixWord ++ tailWord_452556) baseStart_452556 baseEnd_452556 := by
    simpa [prefixWord, tailWord_452556, baseEnd_452556] using wordTrace_append hprefix tailTrace_452556
  have hstable : (prefixWord ++ tailWord_452556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452556).length < 2 ^ (prefixWord ++ tailWord_452556).sum := by decide
  have hdescent : baseEnd_452556 < baseStart_452556 := by decide
  rcases family_descends (prefixWord ++ tailWord_452556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452579 : List Nat := [1, 1, 1, 6, 1, 2, 3, 2, 6]
def baseStart_452579 : Nat := 118140960795 + 452579 * 2 ^ 59
def prefixEnd_452579 : Nat := 4983230072969 + 3 ^ 40 * 452579 * 2
def baseEnd_452579 : Nat := 25821173459032224031237

theorem tailTrace_452579 : CollatzResearch.WordTrace tailWord_452579 prefixEnd_452579 25821173459032224031237 := by
  unfold tailWord_452579
  simp only [CollatzResearch.WordTrace]
  refine ⟨16506912227391052184592791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11004608151594034789728527 16506912227391052184592791)
  ·
    refine ⟨24760368341086578276889187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16506912227391052184592791 24760368341086578276889187)
    ·
      refine ⟨37140552511629867415333781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24760368341086578276889187 37140552511629867415333781)
      ·
        refine ⟨1740963398982650035093771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 37140552511629867415333781 1740963398982650035093771)
        ·
          refine ⟨2611445098473975052640657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1740963398982650035093771 2611445098473975052640657)
          ·
            refine ⟨1958583823855481289480493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2611445098473975052640657 1958583823855481289480493)
            ·
              refine ⟨734468933945805483555185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1958583823855481289480493 734468933945805483555185)
              ·
                refine ⟨550851700459354112666389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 734468933945805483555185 550851700459354112666389)
                ·
                  refine ⟨25821173459032224031237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 550851700459354112666389 25821173459032224031237)
                  ·
                    rfl

theorem cell23_452579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 2, 6].length) (baseStart_452579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_452579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_452579 prefixEnd_452579 := by exact prefixLift 452579
  have htrace : WordTrace (prefixWord ++ tailWord_452579) baseStart_452579 baseEnd_452579 := by
    simpa [prefixWord, tailWord_452579, baseEnd_452579] using wordTrace_append hprefix tailTrace_452579
  have hstable : (prefixWord ++ tailWord_452579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452579).length < 2 ^ (prefixWord ++ tailWord_452579).sum := by decide
  have hdescent : baseEnd_452579 < baseStart_452579 := by decide
  rcases family_descends (prefixWord ++ tailWord_452579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452592 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 5, 5]
def baseStart_452592 : Nat := 118140960795 + 452592 * 2 ^ 59
def prefixEnd_452592 : Nat := 4983230072969 + 3 ^ 40 * 452592 * 2
def baseEnd_452592 : Nat := 77465745459932821806191

theorem tailTrace_452592 : CollatzResearch.WordTrace tailWord_452592 prefixEnd_452592 77465745459932821806191 := by
  unfold tailWord_452592
  simp only [CollatzResearch.WordTrace]
  refine ⟨8253693188171977702408015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11004924250895970269877353 8253693188171977702408015)
  ·
    refine ⟨12380539782257966553612023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8253693188171977702408015 12380539782257966553612023)
    ·
      refine ⟨18570809673386949830418035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12380539782257966553612023 18570809673386949830418035)
      ·
        refine ⟨27856214510080424745627053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18570809673386949830418035 27856214510080424745627053)
        ·
          refine ⟨10446080441280159279610145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27856214510080424745627053 10446080441280159279610145)
          ·
            refine ⟨7834560330960119459707609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10446080441280159279610145 7834560330960119459707609)
            ·
              refine ⟨5875920248220089594780707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7834560330960119459707609 5875920248220089594780707)
              ·
                refine ⟨8813880372330134392171061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5875920248220089594780707 8813880372330134392171061)
                ·
                  refine ⟨826301284905950099266037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8813880372330134392171061 826301284905950099266037)
                  ·
                    refine ⟨77465745459932821806191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 826301284905950099266037 77465745459932821806191)
                    ·
                      rfl

theorem cell23_452592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 5, 5].length) (baseStart_452592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_452592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_452592 prefixEnd_452592 := by exact prefixLift 452592
  have htrace : WordTrace (prefixWord ++ tailWord_452592) baseStart_452592 baseEnd_452592 := by
    simpa [prefixWord, tailWord_452592, baseEnd_452592] using wordTrace_append hprefix tailTrace_452592
  have hstable : (prefixWord ++ tailWord_452592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452592).length < 2 ^ (prefixWord ++ tailWord_452592).sum := by decide
  have hdescent : baseEnd_452592 < baseStart_452592 := by decide
  rcases family_descends (prefixWord ++ tailWord_452592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452616 : List Nat := [2, 1, 3, 2, 1, 2, 2, 3, 2, 3, 2]
def baseStart_452616 : Nat := 118140960795 + 452616 * 2 ^ 59
def prefixEnd_452616 : Nat := 4983230072969 + 3 ^ 40 * 452616 * 2
def baseEnd_452616 : Nat := 232409559915506371518463

theorem tailTrace_452616 : CollatzResearch.WordTrace tailWord_452616 prefixEnd_452616 232409559915506371518463 := by
  unfold tailWord_452616
  simp only [CollatzResearch.WordTrace]
  refine ⟨8254130864128503751844851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11005507818838005002459801 8254130864128503751844851)
  ·
    refine ⟨12381196296192755627767277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8254130864128503751844851 12381196296192755627767277)
    ·
      refine ⟨4642948611072283360412729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12381196296192755627767277 4642948611072283360412729)
      ·
        refine ⟨3482211458304212520309547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4642948611072283360412729 3482211458304212520309547)
        ·
          refine ⟨5223317187456318780464321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3482211458304212520309547 5223317187456318780464321)
          ·
            refine ⟨3917487890592239085348241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5223317187456318780464321 3917487890592239085348241)
            ·
              refine ⟨2938115917944179314011181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3917487890592239085348241 2938115917944179314011181)
              ·
                refine ⟨1101793469229067242754193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2938115917944179314011181 1101793469229067242754193)
                ·
                  refine ⟨826345101921800432065645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1101793469229067242754193 826345101921800432065645)
                  ·
                    refine ⟨309879413220675162024617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 826345101921800432065645 309879413220675162024617)
                    ·
                      refine ⟨232409559915506371518463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 309879413220675162024617 232409559915506371518463)
                      ·
                        rfl

theorem cell23_452616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 2, 3, 2].length) (baseStart_452616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_452616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_452616 prefixEnd_452616 := by exact prefixLift 452616
  have htrace : WordTrace (prefixWord ++ tailWord_452616) baseStart_452616 baseEnd_452616 := by
    simpa [prefixWord, tailWord_452616, baseEnd_452616] using wordTrace_append hprefix tailTrace_452616
  have hstable : (prefixWord ++ tailWord_452616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452616).length < 2 ^ (prefixWord ++ tailWord_452616).sum := by decide
  have hdescent : baseEnd_452616 < baseStart_452616 := by decide
  rcases family_descends (prefixWord ++ tailWord_452616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452639 : List Nat := [1, 1, 2, 4, 1, 2, 1, 3, 4, 4]
def baseStart_452639 : Nat := 118140960795 + 452639 * 2 ^ 59
def prefixEnd_452639 : Nat := 4983230072969 + 3 ^ 40 * 452639 * 2
def baseEnd_452639 : Nat := 77473789990186593843619

theorem tailTrace_452639 : CollatzResearch.WordTrace tailWord_452639 prefixEnd_452639 77473789990186593843619 := by
  unfold tailWord_452639
  simp only [CollatzResearch.WordTrace]
  refine ⟨16509100607173682431776971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11006067071449121621184647 16509100607173682431776971)
  ·
    refine ⟨24763650910760523647665457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16509100607173682431776971 24763650910760523647665457)
    ·
      refine ⟨18572738183070392735749093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24763650910760523647665457 18572738183070392735749093)
      ·
        refine ⟨3482388409325698637952955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18572738183070392735749093 3482388409325698637952955)
        ·
          refine ⟨5223582613988547956929433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3482388409325698637952955 5223582613988547956929433)
          ·
            refine ⟨3917686960491410967697075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5223582613988547956929433 3917686960491410967697075)
            ·
              refine ⟨5876530440737116451545613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3917686960491410967697075 5876530440737116451545613)
              ·
                refine ⟨2203698915276418669329605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5876530440737116451545613 2203698915276418669329605)
                ·
                  refine ⟨413193546614328500499301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2203698915276418669329605 413193546614328500499301)
                  ·
                    refine ⟨77473789990186593843619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 413193546614328500499301 77473789990186593843619)
                    ·
                      rfl

theorem cell23_452639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 4, 4].length) (baseStart_452639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_452639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_452639 prefixEnd_452639 := by exact prefixLift 452639
  have htrace : WordTrace (prefixWord ++ tailWord_452639) baseStart_452639 baseEnd_452639 := by
    simpa [prefixWord, tailWord_452639, baseEnd_452639] using wordTrace_append hprefix tailTrace_452639
  have hstable : (prefixWord ++ tailWord_452639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452639).length < 2 ^ (prefixWord ++ tailWord_452639).sum := by decide
  have hdescent : baseEnd_452639 < baseStart_452639 := by decide
  rcases family_descends (prefixWord ++ tailWord_452639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452656 : List Nat := [2, 1, 1, 1, 2, 6, 1, 3, 2, 4]
def baseStart_452656 : Nat := 118140960795 + 452656 * 2 ^ 59
def prefixEnd_452656 : Nat := 4983230072969 + 3 ^ 40 * 452656 * 2
def baseEnd_452656 : Nat := 77476699713895405006093

theorem tailTrace_452656 : CollatzResearch.WordTrace tailWord_452656 prefixEnd_452656 77476699713895405006093 := by
  unfold tailWord_452656
  simp only [CollatzResearch.WordTrace]
  refine ⟨8254860324056047167572911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11006480432074729556763881 8254860324056047167572911)
  ·
    refine ⟨12382290486084070751359367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8254860324056047167572911 12382290486084070751359367)
    ·
      refine ⟨18573435729126106127039051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12382290486084070751359367 18573435729126106127039051)
      ·
        refine ⟨27860153593689159190558577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18573435729126106127039051 27860153593689159190558577)
        ·
          refine ⟨20895115195266869392918933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27860153593689159190558577 20895115195266869392918933)
          ·
            refine ⟨979458524778134502793075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20895115195266869392918933 979458524778134502793075)
            ·
              refine ⟨1469187787167201754189613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 979458524778134502793075 1469187787167201754189613)
              ·
                refine ⟨550945420187700657821105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1469187787167201754189613 550945420187700657821105)
                ·
                  refine ⟨413209065140775493365829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 550945420187700657821105 413209065140775493365829)
                  ·
                    refine ⟨77476699713895405006093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 413209065140775493365829 77476699713895405006093)
                    ·
                      rfl

theorem cell23_452656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 3, 2, 4].length) (baseStart_452656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_452656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_452656 prefixEnd_452656 := by exact prefixLift 452656
  have htrace : WordTrace (prefixWord ++ tailWord_452656) baseStart_452656 baseEnd_452656 := by
    simpa [prefixWord, tailWord_452656, baseEnd_452656] using wordTrace_append hprefix tailTrace_452656
  have hstable : (prefixWord ++ tailWord_452656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452656).length < 2 ^ (prefixWord ++ tailWord_452656).sum := by decide
  have hdescent : baseEnd_452656 < baseStart_452656 := by decide
  rcases family_descends (prefixWord ++ tailWord_452656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452660 : List Nat := [2, 5, 1, 2, 2, 2, 1, 2, 1, 5]
def baseStart_452660 : Nat := 118140960795 + 452660 * 2 ^ 59
def prefixEnd_452660 : Nat := 4983230072969 + 3 ^ 40 * 452660 * 2
def baseEnd_452660 : Nat := 77477384354768066456087

theorem tailTrace_452660 : CollatzResearch.WordTrace tailWord_452660 prefixEnd_452660 77477384354768066456087 := by
  unfold tailWord_452660
  simp only [CollatzResearch.WordTrace]
  refine ⟨8254933270048801509145717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11006577693398402012194289 8254933270048801509145717)
  ·
    refine ⟨773899994067075141482411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8254933270048801509145717 773899994067075141482411)
    ·
      refine ⟨1160849991100612712223617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 773899994067075141482411 1160849991100612712223617)
      ·
        refine ⟨870637493325459534167713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1160849991100612712223617 870637493325459534167713)
        ·
          refine ⟨652978119994094650625785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 870637493325459534167713 652978119994094650625785)
          ·
            refine ⟨489733589995570987969339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 652978119994094650625785 489733589995570987969339)
            ·
              refine ⟨734600384993356481954009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 489733589995570987969339 734600384993356481954009)
              ·
                refine ⟨550950288745017361465507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 734600384993356481954009 550950288745017361465507)
                ·
                  refine ⟨826425433117526042198261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 550950288745017361465507 826425433117526042198261)
                  ·
                    refine ⟨77477384354768066456087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 826425433117526042198261 77477384354768066456087)
                    ·
                      rfl

theorem cell23_452660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_452660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_452660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_452660 prefixEnd_452660 := by exact prefixLift 452660
  have htrace : WordTrace (prefixWord ++ tailWord_452660) baseStart_452660 baseEnd_452660 := by
    simpa [prefixWord, tailWord_452660, baseEnd_452660] using wordTrace_append hprefix tailTrace_452660
  have hstable : (prefixWord ++ tailWord_452660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452660).length < 2 ^ (prefixWord ++ tailWord_452660).sum := by decide
  have hdescent : baseEnd_452660 < baseStart_452660 := by decide
  rcases family_descends (prefixWord ++ tailWord_452660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452770 : List Nat := [3, 3, 1, 3, 1, 1, 3, 1, 1, 4, 2]
def baseStart_452770 : Nat := 118140960795 + 452770 * 2 ^ 59
def prefixEnd_452770 : Nat := 4983230072969 + 3 ^ 40 * 452770 * 2
def baseEnd_452770 : Nat := 232488635936298768992755

theorem tailTrace_452770 : CollatzResearch.WordTrace tailWord_452770 prefixEnd_452770 232488635936298768992755 := by
  unfold tailWord_452770
  simp only [CollatzResearch.WordTrace]
  refine ⟨4128469642424772951198941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11009252379799394536530509 4128469642424772951198941)
  ·
    refine ⟨1548176115909289856699603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4128469642424772951198941 1548176115909289856699603)
    ·
      refine ⟨2322264173863934785049405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1548176115909289856699603 2322264173863934785049405)
      ·
        refine ⟨870849065198975544393527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2322264173863934785049405 870849065198975544393527)
        ·
          refine ⟨1306273597798463316590291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 870849065198975544393527 1306273597798463316590291)
          ·
            refine ⟨1959410396697694974885437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1306273597798463316590291 1959410396697694974885437)
            ·
              refine ⟨734778898761635615582039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1959410396697694974885437 734778898761635615582039)
              ·
                refine ⟨1102168348142453423373059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 734778898761635615582039 1102168348142453423373059)
                ·
                  refine ⟨1653252522213680135059589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1102168348142453423373059 1653252522213680135059589)
                  ·
                    refine ⟨309984847915065025323673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1653252522213680135059589 309984847915065025323673)
                    ·
                      refine ⟨232488635936298768992755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 309984847915065025323673 232488635936298768992755)
                      ·
                        rfl

theorem cell23_452770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_452770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_452770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_452770 prefixEnd_452770 := by exact prefixLift 452770
  have htrace : WordTrace (prefixWord ++ tailWord_452770) baseStart_452770 baseEnd_452770 := by
    simpa [prefixWord, tailWord_452770, baseEnd_452770] using wordTrace_append hprefix tailTrace_452770
  have hstable : (prefixWord ++ tailWord_452770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452770).length < 2 ^ (prefixWord ++ tailWord_452770).sum := by decide
  have hdescent : baseEnd_452770 < baseStart_452770 := by decide
  rcases family_descends (prefixWord ++ tailWord_452770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452799 : List Nat := [1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 5]
def baseStart_452799 : Nat := 118140960795 + 452799 * 2 ^ 59
def prefixEnd_452799 : Nat := 4983230072969 + 3 ^ 40 * 452799 * 2
def baseEnd_452799 : Nat := 232503526875279155530121

theorem tailTrace_452799 : CollatzResearch.WordTrace tailWord_452799 prefixEnd_452799 232503526875279155530121 := by
  unfold tailWord_452799
  simp only [CollatzResearch.WordTrace]
  refine ⟨16514936286594029757601451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11009957524396019838400967 16514936286594029757601451)
  ·
    refine ⟨24772404429891044636402177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16514936286594029757601451 24772404429891044636402177)
    ·
      refine ⟨18579303322418283477301633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24772404429891044636402177 18579303322418283477301633)
      ·
        refine ⟨13934477491813712607976225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18579303322418283477301633 13934477491813712607976225)
        ·
          refine ⟨10450858118860284455982169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13934477491813712607976225 10450858118860284455982169)
          ·
            refine ⟨7838143589145213341986627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10450858118860284455982169 7838143589145213341986627)
            ·
              refine ⟨11757215383717820012979941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7838143589145213341986627 11757215383717820012979941)
              ·
                refine ⟨2204477884447091252433739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11757215383717820012979941 2204477884447091252433739)
                ·
                  refine ⟨3306716826670636878650609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2204477884447091252433739 3306716826670636878650609)
                  ·
                    refine ⟨2480037620002977658987957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3306716826670636878650609 2480037620002977658987957)
                    ·
                      refine ⟨232503526875279155530121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2480037620002977658987957 232503526875279155530121)
                      ·
                        rfl

theorem cell23_452799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 5].length) (baseStart_452799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_452799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_452799 prefixEnd_452799 := by exact prefixLift 452799
  have htrace : WordTrace (prefixWord ++ tailWord_452799) baseStart_452799 baseEnd_452799 := by
    simpa [prefixWord, tailWord_452799, baseEnd_452799] using wordTrace_append hprefix tailTrace_452799
  have hstable : (prefixWord ++ tailWord_452799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452799).length < 2 ^ (prefixWord ++ tailWord_452799).sum := by decide
  have hdescent : baseEnd_452799 < baseStart_452799 := by decide
  rcases family_descends (prefixWord ++ tailWord_452799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452809 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 3, 3, 4]
def baseStart_452809 : Nat := 118140960795 + 452809 * 2 ^ 59
def prefixEnd_452809 : Nat := 4983230072969 + 3 ^ 40 * 452809 * 2
def baseEnd_452809 : Nat := 232508661681824116405075

theorem tailTrace_452809 : CollatzResearch.WordTrace tailWord_452809 prefixEnd_452809 232508661681824116405075 := by
  unfold tailWord_452809
  simp only [CollatzResearch.WordTrace]
  refine ⟨16515301016557801465465481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11010200677705200976976987 16515301016557801465465481)
  ·
    refine ⟨12386475762418351099099111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16515301016557801465465481 12386475762418351099099111)
    ·
      refine ⟨18579713643627526648648667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12386475762418351099099111 18579713643627526648648667)
      ·
        refine ⟨27869570465441289972973001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18579713643627526648648667 27869570465441289972973001)
        ·
          refine ⟨20902177849080967479729751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27869570465441289972973001 20902177849080967479729751)
          ·
            refine ⟨31353266773621451219594627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20902177849080967479729751 31353266773621451219594627)
            ·
              refine ⟨47029900160432176829391941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31353266773621451219594627 47029900160432176829391941)
              ·
                refine ⟨8818106280081033155510989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47029900160432176829391941 8818106280081033155510989)
                ·
                  refine ⟨3306789855030387433316621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8818106280081033155510989 3306789855030387433316621)
                  ·
                    refine ⟨1240046195636395287493733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3306789855030387433316621 1240046195636395287493733)
                    ·
                      refine ⟨232508661681824116405075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1240046195636395287493733 232508661681824116405075)
                      ·
                        rfl

theorem cell23_452809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 3, 4].length) (baseStart_452809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_452809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_452809 prefixEnd_452809 := by exact prefixLift 452809
  have htrace : WordTrace (prefixWord ++ tailWord_452809) baseStart_452809 baseEnd_452809 := by
    simpa [prefixWord, tailWord_452809, baseEnd_452809] using wordTrace_append hprefix tailTrace_452809
  have hstable : (prefixWord ++ tailWord_452809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452809).length < 2 ^ (prefixWord ++ tailWord_452809).sum := by decide
  have hdescent : baseEnd_452809 < baseStart_452809 := by decide
  rcases family_descends (prefixWord ++ tailWord_452809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452821 : List Nat := [1, 3, 2, 4, 3, 1, 2, 1, 2, 2, 2]
def baseStart_452821 : Nat := 118140960795 + 452821 * 2 ^ 59
def prefixEnd_452821 : Nat := 4983230072969 + 3 ^ 40 * 452821 * 2
def baseEnd_452821 : Nat := 232514823449678069455021

theorem tailTrace_452821 : CollatzResearch.WordTrace tailWord_452821 prefixEnd_452821 232514823449678069455021 := by
  unfold tailWord_452821
  simp only [CollatzResearch.WordTrace]
  refine ⟨16515738692514327514902317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11010492461676218343268211 16515738692514327514902317)
  ·
    refine ⟨6193402009692872818088369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16515738692514327514902317 6193402009692872818088369)
    ·
      refine ⟨4645051507269654613566277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6193402009692872818088369 4645051507269654613566277)
      ·
        refine ⟨870947157613060240043677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4645051507269654613566277 870947157613060240043677)
        ·
          refine ⟨326605184104897590016379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 870947157613060240043677 326605184104897590016379)
          ·
            refine ⟨489907776157346385024569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326605184104897590016379 489907776157346385024569)
            ·
              refine ⟨367430832118009788768427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 489907776157346385024569 367430832118009788768427)
              ·
                refine ⟨551146248177014683152641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367430832118009788768427 551146248177014683152641)
                ·
                  refine ⟨413359686132761012364481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 551146248177014683152641 413359686132761012364481)
                  ·
                    refine ⟨310019764599570759273361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 413359686132761012364481 310019764599570759273361)
                    ·
                      refine ⟨232514823449678069455021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 310019764599570759273361 232514823449678069455021)
                      ·
                        rfl

theorem cell23_452821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_452821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_452821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_452821 prefixEnd_452821 := by exact prefixLift 452821
  have htrace : WordTrace (prefixWord ++ tailWord_452821) baseStart_452821 baseEnd_452821 := by
    simpa [prefixWord, tailWord_452821, baseEnd_452821] using wordTrace_append hprefix tailTrace_452821
  have hstable : (prefixWord ++ tailWord_452821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452821).length < 2 ^ (prefixWord ++ tailWord_452821).sum := by decide
  have hdescent : baseEnd_452821 < baseStart_452821 := by decide
  rcases family_descends (prefixWord ++ tailWord_452821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452836 : List Nat := [2, 3, 1, 1, 1, 2, 1, 3, 5, 4]
def baseStart_452836 : Nat := 118140960795 + 452836 * 2 ^ 59
def prefixEnd_452836 : Nat := 4983230072969 + 3 ^ 40 * 452836 * 2
def baseEnd_452836 : Nat := 77507508553165170255817

theorem tailTrace_452836 : CollatzResearch.WordTrace tailWord_452836 prefixEnd_452836 77507508553165170255817 := by
  unfold tailWord_452836
  simp only [CollatzResearch.WordTrace]
  refine ⟨8258142893729992538349181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11010857191639990051132241 8258142893729992538349181)
  ·
    refine ⟨3096803585148747201880943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8258142893729992538349181 3096803585148747201880943)
    ·
      refine ⟨4645205377723120802821415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3096803585148747201880943 4645205377723120802821415)
      ·
        refine ⟨6967808066584681204232123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4645205377723120802821415 6967808066584681204232123)
        ·
          refine ⟨10451712099877021806348185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6967808066584681204232123 10451712099877021806348185)
          ·
            refine ⟨7838784074907766354761139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10451712099877021806348185 7838784074907766354761139)
            ·
              refine ⟨11758176112361649532141709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7838784074907766354761139 11758176112361649532141709)
              ·
                refine ⟨4409316042135618574553141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11758176112361649532141709 4409316042135618574553141)
                ·
                  refine ⟨413373378950214241364357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4409316042135618574553141 413373378950214241364357)
                  ·
                    refine ⟨77507508553165170255817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 413373378950214241364357 77507508553165170255817)
                    ·
                      rfl

theorem cell23_452836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 5, 4].length) (baseStart_452836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_452836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_452836 prefixEnd_452836 := by exact prefixLift 452836
  have htrace : WordTrace (prefixWord ++ tailWord_452836) baseStart_452836 baseEnd_452836 := by
    simpa [prefixWord, tailWord_452836, baseEnd_452836] using wordTrace_append hprefix tailTrace_452836
  have hstable : (prefixWord ++ tailWord_452836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452836).length < 2 ^ (prefixWord ++ tailWord_452836).sum := by decide
  have hdescent : baseEnd_452836 < baseStart_452836 := by decide
  rcases family_descends (prefixWord ++ tailWord_452836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452849 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 10]
def baseStart_452849 : Nat := 118140960795 + 452849 * 2 ^ 59
def prefixEnd_452849 : Nat := 4983230072969 + 3 ^ 40 * 452849 * 2
def baseEnd_452849 : Nat := 25836577878667106656099

theorem tailTrace_452849 : CollatzResearch.WordTrace tailWord_452849 prefixEnd_452849 25836577878667106656099 := by
  unfold tailWord_452849
  simp only [CollatzResearch.WordTrace]
  refine ⟨16516759936412888296921601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11011173290941925531281067 16516759936412888296921601)
  ·
    refine ⟨12387569952309666222691201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16516759936412888296921601 12387569952309666222691201)
    ·
      refine ⟨9290677464232249667018401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12387569952309666222691201 9290677464232249667018401)
      ·
        refine ⟨6968008098174187250263801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9290677464232249667018401 6968008098174187250263801)
        ·
          refine ⟨5226006073630640437697851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6968008098174187250263801 5226006073630640437697851)
          ·
            refine ⟨7839009110445960656546777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5226006073630640437697851 7839009110445960656546777)
            ·
              refine ⟨5879256832834470492410083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7839009110445960656546777 5879256832834470492410083)
              ·
                refine ⟨8818885249251705738615125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5879256832834470492410083 8818885249251705738615125)
                ·
                  refine ⟨25836577878667106656099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 8818885249251705738615125 25836577878667106656099)
                  ·
                    rfl

theorem cell23_452849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 10].length) (baseStart_452849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_452849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_452849 prefixEnd_452849 := by exact prefixLift 452849
  have htrace : WordTrace (prefixWord ++ tailWord_452849) baseStart_452849 baseEnd_452849 := by
    simpa [prefixWord, tailWord_452849, baseEnd_452849] using wordTrace_append hprefix tailTrace_452849
  have hstable : (prefixWord ++ tailWord_452849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452849).length < 2 ^ (prefixWord ++ tailWord_452849).sum := by decide
  have hdescent : baseEnd_452849 < baseStart_452849 := by decide
  rcases family_descends (prefixWord ++ tailWord_452849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452936 : List Nat := [2, 1, 3, 1, 1, 2, 3, 1, 3, 1, 5]
def baseStart_452936 : Nat := 118140960795 + 452936 * 2 ^ 59
def prefixEnd_452936 : Nat := 4983230072969 + 3 ^ 40 * 452936 * 2
def baseEnd_452936 : Nat := 232573873724945119516991

theorem tailTrace_452936 : CollatzResearch.WordTrace tailWord_452936 prefixEnd_452936 232573873724945119516991 := by
  unfold tailWord_452936
  simp only [CollatzResearch.WordTrace]
  refine ⟨8259966543548851077669331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11013288724731801436892441 8259966543548851077669331)
  ·
    refine ⟨12389949815323276616503997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8259966543548851077669331 12389949815323276616503997)
    ·
      refine ⟨4646231180746228731188999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12389949815323276616503997 4646231180746228731188999)
      ·
        refine ⟨6969346771119343096783499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4646231180746228731188999 6969346771119343096783499)
        ·
          refine ⟨10454020156679014645175249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6969346771119343096783499 10454020156679014645175249)
          ·
            refine ⟨7840515117509260983881437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10454020156679014645175249 7840515117509260983881437)
            ·
              refine ⟨2940193169065972868955539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7840515117509260983881437 2940193169065972868955539)
              ·
                refine ⟨4410289753598959303433309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2940193169065972868955539 4410289753598959303433309)
                ·
                  refine ⟨1653858657599609738787491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4410289753598959303433309 1653858657599609738787491)
                  ·
                    refine ⟨2480787986399414608181237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1653858657599609738787491 2480787986399414608181237)
                    ·
                      refine ⟨232573873724945119516991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2480787986399414608181237 232573873724945119516991)
                      ·
                        rfl

theorem cell23_452936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_452936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_452936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_452936 prefixEnd_452936 := by exact prefixLift 452936
  have htrace : WordTrace (prefixWord ++ tailWord_452936) baseStart_452936 baseEnd_452936 := by
    simpa [prefixWord, tailWord_452936, baseEnd_452936] using wordTrace_append hprefix tailTrace_452936
  have hstable : (prefixWord ++ tailWord_452936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452936).length < 2 ^ (prefixWord ++ tailWord_452936).sum := by decide
  have hdescent : baseEnd_452936 < baseStart_452936 := by decide
  rcases family_descends (prefixWord ++ tailWord_452936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452970 : List Nat := [3, 1, 3, 3, 1, 2, 2, 1, 1, 1, 5]
def baseStart_452970 : Nat := 118140960795 + 452970 * 2 ^ 59
def prefixEnd_452970 : Nat := 4983230072969 + 3 ^ 40 * 452970 * 2
def baseEnd_452970 : Nat := 232591332067197986491835

theorem tailTrace_452970 : CollatzResearch.WordTrace tailWord_452970 prefixEnd_452970 232591332067197986491835 := by
  unfold tailWord_452970
  simp only [CollatzResearch.WordTrace]
  refine ⟨4130293292243631490519091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11014115445983017308050909 4130293292243631490519091)
  ·
    refine ⟨6195439938365447235778637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4130293292243631490519091 6195439938365447235778637)
    ·
      refine ⟨2323289976887042713416989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6195439938365447235778637 2323289976887042713416989)
      ·
        refine ⟨871233741332641017531371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2323289976887042713416989 871233741332641017531371)
        ·
          refine ⟨1306850611998961526297057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 871233741332641017531371 1306850611998961526297057)
          ·
            refine ⟨980137958999221144722793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1306850611998961526297057 980137958999221144722793)
            ·
              refine ⟨735103469249415858542095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 980137958999221144722793 735103469249415858542095)
              ·
                refine ⟨1102655203874123787813143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 735103469249415858542095 1102655203874123787813143)
                ·
                  refine ⟨1653982805811185681719715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1102655203874123787813143 1653982805811185681719715)
                  ·
                    refine ⟨2480974208716778522579573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1653982805811185681719715 2480974208716778522579573)
                    ·
                      refine ⟨232591332067197986491835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2480974208716778522579573 232591332067197986491835)
                      ·
                        rfl

theorem cell23_452970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_452970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_452970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_452970 prefixEnd_452970 := by exact prefixLift 452970
  have htrace : WordTrace (prefixWord ++ tailWord_452970) baseStart_452970 baseEnd_452970 := by
    simpa [prefixWord, tailWord_452970, baseEnd_452970] using wordTrace_append hprefix tailTrace_452970
  have hstable : (prefixWord ++ tailWord_452970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452970).length < 2 ^ (prefixWord ++ tailWord_452970).sum := by decide
  have hdescent : baseEnd_452970 < baseStart_452970 := by decide
  rcases family_descends (prefixWord ++ tailWord_452970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452994 : List Nat := [3, 4, 2, 1, 2, 1, 1, 3, 2, 4]
def baseStart_452994 : Nat := 118140960795 + 452994 * 2 ^ 59
def prefixEnd_452994 : Nat := 4983230072969 + 3 ^ 40 * 452994 * 2
def baseEnd_452994 : Nat := 77534551867635297530575

theorem tailTrace_452994 : CollatzResearch.WordTrace tailWord_452994 prefixEnd_452994 77534551867635297530575 := by
  unfold tailWord_452994
  simp only [CollatzResearch.WordTrace]
  refine ⟨4130512130221894515237509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11014699013925052040633357 4130512130221894515237509)
  ·
    refine ⟨774471024416605221607033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4130512130221894515237509 774471024416605221607033)
    ·
      refine ⟨580853268312453916205275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 774471024416605221607033 580853268312453916205275)
      ·
        refine ⟨871279902468680874307913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580853268312453916205275 871279902468680874307913)
        ·
          refine ⟨653459926851510655730935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 871279902468680874307913 653459926851510655730935)
          ·
            refine ⟨980189890277265983596403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653459926851510655730935 980189890277265983596403)
            ·
              refine ⟨1470284835415898975394605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 980189890277265983596403 1470284835415898975394605)
              ·
                refine ⟨551356813280962115772977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1470284835415898975394605 551356813280962115772977)
                ·
                  refine ⟨413517609960721586829733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 551356813280962115772977 413517609960721586829733)
                  ·
                    refine ⟨77534551867635297530575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 413517609960721586829733 77534551867635297530575)
                    ·
                      rfl

theorem cell23_452994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_452994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_452994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_452994 prefixEnd_452994 := by exact prefixLift 452994
  have htrace : WordTrace (prefixWord ++ tailWord_452994) baseStart_452994 baseEnd_452994 := by
    simpa [prefixWord, tailWord_452994, baseEnd_452994] using wordTrace_append hprefix tailTrace_452994
  have hstable : (prefixWord ++ tailWord_452994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452994).length < 2 ^ (prefixWord ++ tailWord_452994).sum := by decide
  have hdescent : baseEnd_452994 < baseStart_452994 := by decide
  rcases family_descends (prefixWord ++ tailWord_452994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453036 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 6]
def baseStart_453036 : Nat := 118140960795 + 453036 * 2 ^ 59
def prefixEnd_453036 : Nat := 4983230072969 + 3 ^ 40 * 453036 * 2
def baseEnd_453036 : Nat := 232625221790394728266531

theorem tailTrace_453036 : CollatzResearch.WordTrace tailWord_453036 prefixEnd_453036 232625221790394728266531 := by
  unfold tailWord_453036
  simp only [CollatzResearch.WordTrace]
  refine ⟨8261790193367709616989481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11015720257823612822652641 8261790193367709616989481)
  ·
    refine ⟨6196342645025782212742111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8261790193367709616989481 6196342645025782212742111)
    ·
      refine ⟨9294513967538673319113167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6196342645025782212742111 9294513967538673319113167)
      ·
        refine ⟨13941770951308009978669751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9294513967538673319113167 13941770951308009978669751)
        ·
          refine ⟨20912656426962014968004627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13941770951308009978669751 20912656426962014968004627)
          ·
            refine ⟨31368984640443022452006941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20912656426962014968004627 31368984640443022452006941)
            ·
              refine ⟨11763369240166133419502603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31368984640443022452006941 11763369240166133419502603)
              ·
                refine ⟨17645053860249200129253905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11763369240166133419502603 17645053860249200129253905)
                ·
                  refine ⟨13233790395186900096940429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17645053860249200129253905 13233790395186900096940429)
                  ·
                    refine ⟨4962671398195087536352661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13233790395186900096940429 4962671398195087536352661)
                    ·
                      refine ⟨232625221790394728266531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4962671398195087536352661 232625221790394728266531)
                      ·
                        rfl

theorem cell23_453036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_453036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_453036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_453036 prefixEnd_453036 := by exact prefixLift 453036
  have htrace : WordTrace (prefixWord ++ tailWord_453036) baseStart_453036 baseEnd_453036 := by
    simpa [prefixWord, tailWord_453036, baseEnd_453036] using wordTrace_append hprefix tailTrace_453036
  have hstable : (prefixWord ++ tailWord_453036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453036).length < 2 ^ (prefixWord ++ tailWord_453036).sum := by decide
  have hdescent : baseEnd_453036 < baseStart_453036 := by decide
  rcases family_descends (prefixWord ++ tailWord_453036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453040 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 8, 2, 2]
def baseStart_453040 : Nat := 118140960795 + 453040 * 2 ^ 59
def prefixEnd_453040 : Nat := 4983230072969 + 3 ^ 40 * 453040 * 2
def baseEnd_453040 : Nat := 232627275713012712616513

theorem tailTrace_453040 : CollatzResearch.WordTrace tailWord_453040 prefixEnd_453040 232627275713012712616513 := by
  unfold tailWord_453040
  simp only [CollatzResearch.WordTrace]
  refine ⟨8261863139360463958562287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11015817519147285278083049 8261863139360463958562287)
  ·
    refine ⟨12392794709040695937843431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8261863139360463958562287 12392794709040695937843431)
    ·
      refine ⟨18589192063561043906765147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12392794709040695937843431 18589192063561043906765147)
      ·
        refine ⟨27883788095341565860147721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18589192063561043906765147 27883788095341565860147721)
        ·
          refine ⟨20912841071506174395110791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27883788095341565860147721 20912841071506174395110791)
          ·
            refine ⟨31369261607259261592666187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20912841071506174395110791 31369261607259261592666187)
            ·
              refine ⟨47053892410888892388999281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31369261607259261592666187 47053892410888892388999281)
              ·
                refine ⟨35290419308166669291749461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47053892410888892388999281 35290419308166669291749461)
                ·
                  refine ⟨413559601267578155762689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35290419308166669291749461 413559601267578155762689)
                  ·
                    refine ⟨310169700950683616822017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 413559601267578155762689 310169700950683616822017)
                    ·
                      refine ⟨232627275713012712616513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 310169700950683616822017 232627275713012712616513)
                      ·
                        rfl

theorem cell23_453040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 8, 2, 2].length) (baseStart_453040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_453040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_453040 prefixEnd_453040 := by exact prefixLift 453040
  have htrace : WordTrace (prefixWord ++ tailWord_453040) baseStart_453040 baseEnd_453040 := by
    simpa [prefixWord, tailWord_453040, baseEnd_453040] using wordTrace_append hprefix tailTrace_453040
  have hstable : (prefixWord ++ tailWord_453040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453040).length < 2 ^ (prefixWord ++ tailWord_453040).sum := by decide
  have hdescent : baseEnd_453040 < baseStart_453040 := by decide
  rcases family_descends (prefixWord ++ tailWord_453040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453053 : List Nat := [1, 4, 1, 2, 2, 2, 1, 1, 1, 4, 4]
def baseStart_453053 : Nat := 118140960795 + 453053 * 2 ^ 59
def prefixEnd_453053 : Nat := 4983230072969 + 3 ^ 40 * 453053 * 2
def baseEnd_453053 : Nat := 232633950961521161753953

theorem tailTrace_453053 : CollatzResearch.WordTrace tailWord_453053 prefixEnd_453053 232633950961521161753953 := by
  unfold tailWord_453053
  simp only [CollatzResearch.WordTrace]
  refine ⟨16524200427673831137347813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11016133618449220758231875 16524200427673831137347813)
  ·
    refine ⟨3098287580188843338252715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16524200427673831137347813 3098287580188843338252715)
    ·
      refine ⟨4647431370283265007379073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3098287580188843338252715 4647431370283265007379073)
      ·
        refine ⟨3485573527712448755534305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4647431370283265007379073 3485573527712448755534305)
        ·
          refine ⟨2614180145784336566650729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3485573527712448755534305 2614180145784336566650729)
          ·
            refine ⟨1960635109338252424988047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2614180145784336566650729 1960635109338252424988047)
            ·
              refine ⟨2940952664007378637482071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1960635109338252424988047 2940952664007378637482071)
              ·
                refine ⟨4411428996011067956223107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2940952664007378637482071 4411428996011067956223107)
                ·
                  refine ⟨6617143494016601934334661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4411428996011067956223107 6617143494016601934334661)
                  ·
                    refine ⟨1240714405128112862687749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6617143494016601934334661 1240714405128112862687749)
                    ·
                      refine ⟨232633950961521161753953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1240714405128112862687749 232633950961521161753953)
                      ·
                        rfl

theorem cell23_453053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_453053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_453053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_453053 prefixEnd_453053 := by exact prefixLift 453053
  have htrace : WordTrace (prefixWord ++ tailWord_453053) baseStart_453053 baseEnd_453053 := by
    simpa [prefixWord, tailWord_453053, baseEnd_453053] using wordTrace_append hprefix tailTrace_453053
  have hstable : (prefixWord ++ tailWord_453053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453053).length < 2 ^ (prefixWord ++ tailWord_453053).sum := by decide
  have hdescent : baseEnd_453053 < baseStart_453053 := by decide
  rcases family_descends (prefixWord ++ tailWord_453053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453063 : List Nat := [1, 1, 4, 1, 1, 5, 1, 2, 7]
def baseStart_453063 : Nat := 118140960795 + 453063 * 2 ^ 59
def prefixEnd_453063 : Nat := 4983230072969 + 3 ^ 40 * 453063 * 2
def baseEnd_453063 : Nat := 25848787307562902514323

theorem tailTrace_453063 : CollatzResearch.WordTrace tailWord_453063 prefixEnd_453063 25848787307562902514323 := by
  unfold tailWord_453063
  simp only [CollatzResearch.WordTrace]
  refine ⟨16524565157637602845211843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11016376771758401896807895 16524565157637602845211843)
  ·
    refine ⟨24786847736456404267817765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16524565157637602845211843 24786847736456404267817765)
    ·
      refine ⟨4647533950585575800215831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24786847736456404267817765 4647533950585575800215831)
      ·
        refine ⟨6971300925878363700323747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4647533950585575800215831 6971300925878363700323747)
        ·
          refine ⟨10456951388817545550485621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6971300925878363700323747 10456951388817545550485621)
          ·
            refine ⟨980339192701644895358027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10456951388817545550485621 980339192701644895358027)
            ·
              refine ⟨1470508789052467343037041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 980339192701644895358027 1470508789052467343037041)
              ·
                refine ⟨1102881591789350507277781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1470508789052467343037041 1102881591789350507277781)
                ·
                  refine ⟨25848787307562902514323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1102881591789350507277781 25848787307562902514323)
                  ·
                    rfl

theorem cell23_453063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 7].length) (baseStart_453063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_453063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_453063 prefixEnd_453063 := by exact prefixLift 453063
  have htrace : WordTrace (prefixWord ++ tailWord_453063) baseStart_453063 baseEnd_453063 := by
    simpa [prefixWord, tailWord_453063, baseEnd_453063] using wordTrace_append hprefix tailTrace_453063
  have hstable : (prefixWord ++ tailWord_453063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453063).length < 2 ^ (prefixWord ++ tailWord_453063).sum := by decide
  have hdescent : baseEnd_453063 < baseStart_453063 := by decide
  rcases family_descends (prefixWord ++ tailWord_453063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453091 : List Nat := [1, 1, 1, 6, 3, 2, 1, 2, 2, 2, 2]
def baseStart_453091 : Nat := 118140960795 + 453091 * 2 ^ 59
def prefixEnd_453091 : Nat := 4983230072969 + 3 ^ 40 * 453091 * 2
def baseEnd_453091 : Nat := 232653463226392013078779

theorem tailTrace_453091 : CollatzResearch.WordTrace tailWord_453091 prefixEnd_453091 232653463226392013078779 := by
  unfold tailWord_453091
  simp only [CollatzResearch.WordTrace]
  refine ⟨16525586401536163627231127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11017057601024109084820751 16525586401536163627231127)
  ·
    refine ⟨24788379602304245440846691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16525586401536163627231127 24788379602304245440846691)
    ·
      refine ⟨37182569403456368161270037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24788379602304245440846691 37182569403456368161270037)
      ·
        refine ⟨1742932940787017257559533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 37182569403456368161270037 1742932940787017257559533)
        ·
          refine ⟨653599852795131471584825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1742932940787017257559533 653599852795131471584825)
          ·
            refine ⟨490199889596348603688619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 653599852795131471584825 490199889596348603688619)
            ·
              refine ⟨735299834394522905532929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 490199889596348603688619 735299834394522905532929)
              ·
                refine ⟨551474875795892179149697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 735299834394522905532929 551474875795892179149697)
                ·
                  refine ⟨413606156846919134362273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 551474875795892179149697 413606156846919134362273)
                  ·
                    refine ⟨310204617635189350771705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 413606156846919134362273 310204617635189350771705)
                    ·
                      refine ⟨232653463226392013078779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 310204617635189350771705 232653463226392013078779)
                      ·
                        rfl

theorem cell23_453091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_453091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_453091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_453091 prefixEnd_453091 := by exact prefixLift 453091
  have htrace : WordTrace (prefixWord ++ tailWord_453091) baseStart_453091 baseEnd_453091 := by
    simpa [prefixWord, tailWord_453091, baseEnd_453091] using wordTrace_append hprefix tailTrace_453091
  have hstable : (prefixWord ++ tailWord_453091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453091).length < 2 ^ (prefixWord ++ tailWord_453091).sum := by decide
  have hdescent : baseEnd_453091 < baseStart_453091 := by decide
  rcases family_descends (prefixWord ++ tailWord_453091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453113 : List Nat := [1, 2, 1, 3, 1, 2, 3, 2, 1, 3, 4]
def baseStart_453113 : Nat := 118140960795 + 453113 * 2 ^ 59
def prefixEnd_453113 : Nat := 4983230072969 + 3 ^ 40 * 453113 * 2
def baseEnd_453113 : Nat := 232664759800790927003677

theorem tailTrace_453113 : CollatzResearch.WordTrace tailWord_453113 prefixEnd_453113 232664759800790927003677 := by
  unfold tailWord_453113
  simp only [CollatzResearch.WordTrace]
  refine ⟨16526388807456461384531993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11017592538304307589687995 16526388807456461384531993)
  ·
    refine ⟨12394791605592346038398995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16526388807456461384531993 12394791605592346038398995)
    ·
      refine ⟨18592187408388519057598493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12394791605592346038398995 18592187408388519057598493)
      ·
        refine ⟨6972070278145694646599435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18592187408388519057598493 6972070278145694646599435)
        ·
          refine ⟨10458105417218541969899153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6972070278145694646599435 10458105417218541969899153)
          ·
            refine ⟨7843579062913906477424365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10458105417218541969899153 7843579062913906477424365)
            ·
              refine ⟨2941342148592714929034137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7843579062913906477424365 2941342148592714929034137)
              ·
                refine ⟨2206006611444536196775603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2941342148592714929034137 2206006611444536196775603)
                ·
                  refine ⟨3309009917166804295163405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2206006611444536196775603 3309009917166804295163405)
                  ·
                    refine ⟨1240878718937551610686277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3309009917166804295163405 1240878718937551610686277)
                    ·
                      refine ⟨232664759800790927003677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1240878718937551610686277 232664759800790927003677)
                      ·
                        rfl

theorem cell23_453113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_453113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_453113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_453113 prefixEnd_453113 := by exact prefixLift 453113
  have htrace : WordTrace (prefixWord ++ tailWord_453113) baseStart_453113 baseEnd_453113 := by
    simpa [prefixWord, tailWord_453113, baseEnd_453113] using wordTrace_append hprefix tailTrace_453113
  have hstable : (prefixWord ++ tailWord_453113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453113).length < 2 ^ (prefixWord ++ tailWord_453113).sum := by decide
  have hdescent : baseEnd_453113 < baseStart_453113 := by decide
  rcases family_descends (prefixWord ++ tailWord_453113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453130 : List Nat := [3, 1, 2, 2, 2, 1, 2, 3, 2, 1, 4]
def baseStart_453130 : Nat := 118140960795 + 453130 * 2 ^ 59
def prefixEnd_453130 : Nat := 4983230072969 + 3 ^ 40 * 453130 * 2
def baseEnd_453130 : Nat := 232673488971917360491099

theorem tailTrace_453130 : CollatzResearch.WordTrace tailWord_453130 prefixEnd_453130 232673488971917360491099 := by
  unfold tailWord_453130
  simp only [CollatzResearch.WordTrace]
  refine ⟨4131752212098718321975211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11018005898929915525267229 4131752212098718321975211)
  ·
    refine ⟨6197628318148077482962817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4131752212098718321975211 6197628318148077482962817)
    ·
      refine ⟨4648221238611058112222113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6197628318148077482962817 4648221238611058112222113)
      ·
        refine ⟨3486165928958293584166585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4648221238611058112222113 3486165928958293584166585)
        ·
          refine ⟨2614624446718720188124939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3486165928958293584166585 2614624446718720188124939)
          ·
            refine ⟨3921936670078080282187409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2614624446718720188124939 3921936670078080282187409)
            ·
              refine ⟨2941452502558560211640557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3921936670078080282187409 2941452502558560211640557)
              ·
                refine ⟨1103044688459460079365209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2941452502558560211640557 1103044688459460079365209)
                ·
                  refine ⟨827283516344595059523907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1103044688459460079365209 827283516344595059523907)
                  ·
                    refine ⟨1240925274516892589285861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 827283516344595059523907 1240925274516892589285861)
                    ·
                      refine ⟨232673488971917360491099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1240925274516892589285861 232673488971917360491099)
                      ·
                        rfl

theorem cell23_453130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_453130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_453130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_453130 prefixEnd_453130 := by exact prefixLift 453130
  have htrace : WordTrace (prefixWord ++ tailWord_453130) baseStart_453130 baseEnd_453130 := by
    simpa [prefixWord, tailWord_453130, baseEnd_453130] using wordTrace_append hprefix tailTrace_453130
  have hstable : (prefixWord ++ tailWord_453130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453130).length < 2 ^ (prefixWord ++ tailWord_453130).sum := by decide
  have hdescent : baseEnd_453130 < baseStart_453130 := by decide
  rcases family_descends (prefixWord ++ tailWord_453130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453153 : List Nat := [1, 2, 3, 2, 2, 1, 1, 3, 8]
def baseStart_453153 : Nat := 118140960795 + 453153 * 2 ^ 59
def prefixEnd_453153 : Nat := 4983230072969 + 3 ^ 40 * 453153 * 2
def baseEnd_453153 : Nat := 25853922114107863389277

theorem tailTrace_453153 : CollatzResearch.WordTrace tailWord_453153 prefixEnd_453153 25853922114107863389277 := by
  unfold tailWord_453153
  simp only [CollatzResearch.WordTrace]
  refine ⟨16527847727311548215988113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11018565151541032143992075 16527847727311548215988113)
  ·
    refine ⟨12395885795483661161991085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16527847727311548215988113 12395885795483661161991085)
    ·
      refine ⟨4648457173306372935746657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12395885795483661161991085 4648457173306372935746657)
      ·
        refine ⟨3486342879979779701809993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4648457173306372935746657 3486342879979779701809993)
        ·
          refine ⟨2614757159984834776357495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3486342879979779701809993 2614757159984834776357495)
          ·
            refine ⟨3922135739977252164536243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2614757159984834776357495 3922135739977252164536243)
            ·
              refine ⟨5883203609965878246804365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3922135739977252164536243 5883203609965878246804365)
              ·
                refine ⟨2206201353737204342551637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5883203609965878246804365 2206201353737204342551637)
                ·
                  refine ⟨25853922114107863389277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2206201353737204342551637 25853922114107863389277)
                  ·
                    rfl

theorem cell23_453153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 8].length) (baseStart_453153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_453153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_453153 prefixEnd_453153 := by exact prefixLift 453153
  have htrace : WordTrace (prefixWord ++ tailWord_453153) baseStart_453153 baseEnd_453153 := by
    simpa [prefixWord, tailWord_453153, baseEnd_453153] using wordTrace_append hprefix tailTrace_453153
  have hstable : (prefixWord ++ tailWord_453153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453153).length < 2 ^ (prefixWord ++ tailWord_453153).sum := by decide
  have hdescent : baseEnd_453153 < baseStart_453153 := by decide
  rcases family_descends (prefixWord ++ tailWord_453153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453157 : List Nat := [1, 3, 1, 2, 2, 1, 2, 6, 1, 4]
def baseStart_453157 : Nat := 118140960795 + 453157 * 2 ^ 59
def prefixEnd_453157 : Nat := 4983230072969 + 3 ^ 40 * 453157 * 2
def baseEnd_453157 : Nat := 77562450983196251617825

theorem tailTrace_453157 : CollatzResearch.WordTrace tailWord_453157 prefixEnd_453157 77562450983196251617825 := by
  unfold tailWord_453157
  simp only [CollatzResearch.WordTrace]
  refine ⟨16527993619297056899133725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11018662412864704599422483 16527993619297056899133725)
  ·
    refine ⟨6197997607236396337175147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16527993619297056899133725 6197997607236396337175147)
    ·
      refine ⟨9296996410854594505762721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6197997607236396337175147 9296996410854594505762721)
      ·
        refine ⟨6972747308140945879322041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9296996410854594505762721 6972747308140945879322041)
        ·
          refine ⟨5229560481105709409491531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6972747308140945879322041 5229560481105709409491531)
          ·
            refine ⟨7844340721658564114237297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5229560481105709409491531 7844340721658564114237297)
            ·
              refine ⟨5883255541243923085677973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7844340721658564114237297 5883255541243923085677973)
              ·
                refine ⟨275777603495808894641155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5883255541243923085677973 275777603495808894641155)
                ·
                  refine ⟨413666405243713341961733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 275777603495808894641155 413666405243713341961733)
                  ·
                    refine ⟨77562450983196251617825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 413666405243713341961733 77562450983196251617825)
                    ·
                      rfl

theorem cell23_453157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 6, 1, 4].length) (baseStart_453157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_453157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_453157 prefixEnd_453157 := by exact prefixLift 453157
  have htrace : WordTrace (prefixWord ++ tailWord_453157) baseStart_453157 baseEnd_453157 := by
    simpa [prefixWord, tailWord_453157, baseEnd_453157] using wordTrace_append hprefix tailTrace_453157
  have hstable : (prefixWord ++ tailWord_453157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453157).length < 2 ^ (prefixWord ++ tailWord_453157).sum := by decide
  have hdescent : baseEnd_453157 < baseStart_453157 := by decide
  rcases family_descends (prefixWord ++ tailWord_453157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453207 : List Nat := [1, 1, 3, 2, 2, 2, 1, 4, 2, 3, 2]
def baseStart_453207 : Nat := 118140960795 + 453207 * 2 ^ 59
def prefixEnd_453207 : Nat := 4983230072969 + 3 ^ 40 * 453207 * 2
def baseEnd_453207 : Nat := 232713026982313559228245

theorem tailTrace_453207 : CollatzResearch.WordTrace tailWord_453207 prefixEnd_453207 232713026982313559228245 := by
  unfold tailWord_453207
  simp only [CollatzResearch.WordTrace]
  refine ⟨16529817269115915438453875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11019878179410610292302583 16529817269115915438453875)
  ·
    refine ⟨24794725903673873157680813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16529817269115915438453875 24794725903673873157680813)
    ·
      refine ⟨9298022213877702434130305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24794725903673873157680813 9298022213877702434130305)
      ·
        refine ⟨6973516660408276825597729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9298022213877702434130305 6973516660408276825597729)
        ·
          refine ⟨5230137495306207619198297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6973516660408276825597729 5230137495306207619198297)
          ·
            refine ⟨3922603121479655714398723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5230137495306207619198297 3922603121479655714398723)
            ·
              refine ⟨5883904682219483571598085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3922603121479655714398723 5883904682219483571598085)
              ·
                refine ⟨1103232127916153169674641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5883904682219483571598085 1103232127916153169674641)
                ·
                  refine ⟨827424095937114877255981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1103232127916153169674641 827424095937114877255981)
                  ·
                    refine ⟨310284035976418078970993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 827424095937114877255981 310284035976418078970993)
                    ·
                      refine ⟨232713026982313559228245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 310284035976418078970993 232713026982313559228245)
                      ·
                        rfl

theorem cell23_453207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 2, 3, 2].length) (baseStart_453207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_453207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_453207 prefixEnd_453207 := by exact prefixLift 453207
  have htrace : WordTrace (prefixWord ++ tailWord_453207) baseStart_453207 baseEnd_453207 := by
    simpa [prefixWord, tailWord_453207, baseEnd_453207] using wordTrace_append hprefix tailTrace_453207
  have hstable : (prefixWord ++ tailWord_453207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453207).length < 2 ^ (prefixWord ++ tailWord_453207).sum := by decide
  have hdescent : baseEnd_453207 < baseStart_453207 := by decide
  rcases family_descends (prefixWord ++ tailWord_453207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453220 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4]
def baseStart_453220 : Nat := 118140960795 + 453220 * 2 ^ 59
def prefixEnd_453220 : Nat := 4983230072969 + 3 ^ 40 * 453220 * 2
def baseEnd_453220 : Nat := 232719702230822008365685

theorem tailTrace_453220 : CollatzResearch.WordTrace tailWord_453220 prefixEnd_453220 232719702230822008365685 := by
  unfold tailWord_453220
  simp only [CollatzResearch.WordTrace]
  refine ⟨8265145709034409329338557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11020194278712545772451409 8265145709034409329338557)
  ·
    refine ⟨3099429640887903498501959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8265145709034409329338557 3099429640887903498501959)
    ·
      refine ⟨4649144461331855247752939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3099429640887903498501959 4649144461331855247752939)
      ·
        refine ⟨6973716691997782871629409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4649144461331855247752939 6973716691997782871629409)
        ·
          refine ⟨5230287518998337153722057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6973716691997782871629409 5230287518998337153722057)
          ·
            refine ⟨3922715639248752865291543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5230287518998337153722057 3922715639248752865291543)
            ·
              refine ⟨5884073458873129297937315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3922715639248752865291543 5884073458873129297937315)
              ·
                refine ⟨8826110188309693946905973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5884073458873129297937315 8826110188309693946905973)
                ·
                  refine ⟨827447830154033807522435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8826110188309693946905973 827447830154033807522435)
                  ·
                    refine ⟨1241171745231050711283653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 827447830154033807522435 1241171745231050711283653)
                    ·
                      refine ⟨232719702230822008365685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1241171745231050711283653 232719702230822008365685)
                      ·
                        rfl

theorem cell23_453220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_453220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_453220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_453220 prefixEnd_453220 := by exact prefixLift 453220
  have htrace : WordTrace (prefixWord ++ tailWord_453220) baseStart_453220 baseEnd_453220 := by
    simpa [prefixWord, tailWord_453220, baseEnd_453220] using wordTrace_append hprefix tailTrace_453220
  have hstable : (prefixWord ++ tailWord_453220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453220).length < 2 ^ (prefixWord ++ tailWord_453220).sum := by decide
  have hdescent : baseEnd_453220 < baseStart_453220 := by decide
  rcases family_descends (prefixWord ++ tailWord_453220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453271 : List Nat := [1, 1, 3, 3, 2, 1, 1, 6, 1, 2, 2]
def baseStart_453271 : Nat := 118140960795 + 453271 * 2 ^ 59
def prefixEnd_453271 : Nat := 4983230072969 + 3 ^ 40 * 453271 * 2
def baseEnd_453271 : Nat := 232745889744201308827951

theorem tailTrace_453271 : CollatzResearch.WordTrace tailWord_453271 prefixEnd_453271 232745889744201308827951 := by
  unfold tailWord_453271
  simp only [CollatzResearch.WordTrace]
  refine ⟨16532151540884054368783667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11021434360589369579189111 16532151540884054368783667)
  ·
    refine ⟨24798227311326081553175501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16532151540884054368783667 24798227311326081553175501)
    ·
      refine ⟨9299335241747280582440813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24798227311326081553175501 9299335241747280582440813)
      ·
        refine ⟨3487250715655230218415305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9299335241747280582440813 3487250715655230218415305)
        ·
          refine ⟨2615438036741422663811479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3487250715655230218415305 2615438036741422663811479)
          ·
            refine ⟨3923157055112133995717219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2615438036741422663811479 3923157055112133995717219)
            ·
              refine ⟨5884735582668200993575829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3923157055112133995717219 5884735582668200993575829)
              ·
                refine ⟨275846980437571921573867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5884735582668200993575829 275846980437571921573867)
                ·
                  refine ⟨413770470656357882360801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 275846980437571921573867 413770470656357882360801)
                  ·
                    refine ⟨310327852992268411770601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 413770470656357882360801 310327852992268411770601)
                    ·
                      refine ⟨232745889744201308827951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 310327852992268411770601 232745889744201308827951)
                      ·
                        rfl

theorem cell23_453271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 6, 1, 2, 2].length) (baseStart_453271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_453271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_453271 prefixEnd_453271 := by exact prefixLift 453271
  have htrace : WordTrace (prefixWord ++ tailWord_453271) baseStart_453271 baseEnd_453271 := by
    simpa [prefixWord, tailWord_453271, baseEnd_453271] using wordTrace_append hprefix tailTrace_453271
  have hstable : (prefixWord ++ tailWord_453271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453271).length < 2 ^ (prefixWord ++ tailWord_453271).sum := by decide
  have hdescent : baseEnd_453271 < baseStart_453271 := by decide
  rcases family_descends (prefixWord ++ tailWord_453271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453274 : List Nat := [3, 1, 1, 6, 1, 1, 1, 2, 1, 1, 5]
def baseStart_453274 : Nat := 118140960795 + 453274 * 2 ^ 59
def prefixEnd_453274 : Nat := 4983230072969 + 3 ^ 40 * 453274 * 2
def baseEnd_453274 : Nat := 232747430186164797090437

theorem tailTrace_453274 : CollatzResearch.WordTrace tailWord_453274 prefixEnd_453274 232747430186164797090437 := by
  unfold tailWord_453274
  simp only [CollatzResearch.WordTrace]
  refine ⟨4133065239968296470285719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11021507306582123920761917 4133065239968296470285719)
  ·
    refine ⟨6199597859952444705428579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4133065239968296470285719 6199597859952444705428579)
    ·
      refine ⟨9299396789928667058142869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6199597859952444705428579 9299396789928667058142869)
      ·
        refine ⟨435909224527906268350447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9299396789928667058142869 435909224527906268350447)
        ·
          refine ⟨653863836791859402525671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435909224527906268350447 653863836791859402525671)
          ·
            refine ⟨980795755187789103788507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653863836791859402525671 980795755187789103788507)
            ·
              refine ⟨1471193632781683655682761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 980795755187789103788507 1471193632781683655682761)
              ·
                refine ⟨1103395224586262741762071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1471193632781683655682761 1103395224586262741762071)
                ·
                  refine ⟨1655092836879394112643107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1103395224586262741762071 1655092836879394112643107)
                  ·
                    refine ⟨2482639255319091168964661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1655092836879394112643107 2482639255319091168964661)
                    ·
                      refine ⟨232747430186164797090437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2482639255319091168964661 232747430186164797090437)
                      ·
                        rfl

theorem cell23_453274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_453274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_453274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_453274 prefixEnd_453274 := by exact prefixLift 453274
  have htrace : WordTrace (prefixWord ++ tailWord_453274) baseStart_453274 baseEnd_453274 := by
    simpa [prefixWord, tailWord_453274, baseEnd_453274] using wordTrace_append hprefix tailTrace_453274
  have hstable : (prefixWord ++ tailWord_453274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453274).length < 2 ^ (prefixWord ++ tailWord_453274).sum := by decide
  have hdescent : baseEnd_453274 < baseStart_453274 := by decide
  rcases family_descends (prefixWord ++ tailWord_453274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453281 : List Nat := [1, 2, 3, 3, 3, 1, 3, 1, 2, 4]
def baseStart_453281 : Nat := 118140960795 + 453281 * 2 ^ 59
def prefixEnd_453281 : Nat := 4983230072969 + 3 ^ 40 * 453281 * 2
def baseEnd_453281 : Nat := 77583674850248756567635

theorem tailTrace_453281 : CollatzResearch.WordTrace tailWord_453281 prefixEnd_453281 77583674850248756567635 := by
  unfold tailWord_453281
  simp only [CollatzResearch.WordTrace]
  refine ⟨16532516270847826076647697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11021677513898550717765131 16532516270847826076647697)
  ·
    refine ⟨12399387203135869557485773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16532516270847826076647697 12399387203135869557485773)
    ·
      refine ⟨4649770201175951084057165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12399387203135869557485773 4649770201175951084057165)
      ·
        refine ⟨1743663825440981656521437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4649770201175951084057165 1743663825440981656521437)
        ·
          refine ⟨653873934540368121195539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1743663825440981656521437 653873934540368121195539)
          ·
            refine ⟨980810901810552181793309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653873934540368121195539 980810901810552181793309)
            ·
              refine ⟨367804088178957068172491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 980810901810552181793309 367804088178957068172491)
              ·
                refine ⟨551706132268435602258737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367804088178957068172491 551706132268435602258737)
                ·
                  refine ⟨413779599201326701694053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 551706132268435602258737 413779599201326701694053)
                  ·
                    refine ⟨77583674850248756567635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 413779599201326701694053 77583674850248756567635)
                    ·
                      rfl

theorem cell23_453281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 1, 2, 4].length) (baseStart_453281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_453281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_453281 prefixEnd_453281 := by exact prefixLift 453281
  have htrace : WordTrace (prefixWord ++ tailWord_453281) baseStart_453281 baseEnd_453281 := by
    simpa [prefixWord, tailWord_453281, baseEnd_453281] using wordTrace_append hprefix tailTrace_453281
  have hstable : (prefixWord ++ tailWord_453281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453281).length < 2 ^ (prefixWord ++ tailWord_453281).sum := by decide
  have hdescent : baseEnd_453281 < baseStart_453281 := by decide
  rcases family_descends (prefixWord ++ tailWord_453281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453294 : List Nat := [4, 1, 4, 1, 1, 1, 4, 7]
def baseStart_453294 : Nat := 118140960795 + 453294 * 2 ^ 59
def prefixEnd_453294 : Nat := 4983230072969 + 3 ^ 40 * 453294 * 2
def baseEnd_453294 : Nat := 8620655548120545142235

theorem tailTrace_453294 : CollatzResearch.WordTrace tailWord_453294 prefixEnd_453294 8620655548120545142235 := by
  unfold tailWord_453294
  simp only [CollatzResearch.WordTrace]
  refine ⟨2066623802475091162108867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11021993613200486197913957 2066623802475091162108867)
  ·
    refine ⟨3099935703712636743163301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2066623802475091162108867 3099935703712636743163301)
    ·
      refine ⟨581237944446119389343119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3099935703712636743163301 581237944446119389343119)
      ·
        refine ⟨871856916669179084014679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 581237944446119389343119 871856916669179084014679)
        ·
          refine ⟨1307785375003768626022019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 871856916669179084014679 1307785375003768626022019)
          ·
            refine ⟨1961678062505652939033029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1307785375003768626022019 1961678062505652939033029)
            ·
              refine ⟨367814636719809926068693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1961678062505652939033029 367814636719809926068693)
              ·
                refine ⟨8620655548120545142235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 367814636719809926068693 8620655548120545142235)
                ·
                  rfl

theorem cell23_453294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 7].length) (baseStart_453294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_453294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_453294 prefixEnd_453294 := by exact prefixLift 453294
  have htrace : WordTrace (prefixWord ++ tailWord_453294) baseStart_453294 baseEnd_453294 := by
    simpa [prefixWord, tailWord_453294, baseEnd_453294] using wordTrace_append hprefix tailTrace_453294
  have hstable : (prefixWord ++ tailWord_453294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453294).length < 2 ^ (prefixWord ++ tailWord_453294).sum := by decide
  have hdescent : baseEnd_453294 < baseStart_453294 := by decide
  rcases family_descends (prefixWord ++ tailWord_453294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453347 : List Nat := [1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 5]
def baseStart_453347 : Nat := 118140960795 + 453347 * 2 ^ 59
def prefixEnd_453347 : Nat := 4983230072969 + 3 ^ 40 * 453347 * 2
def baseEnd_453347 : Nat := 232784914273943011477601

theorem tailTrace_453347 : CollatzResearch.WordTrace tailWord_453347 prefixEnd_453347 232784914273943011477601 := by
  unfold tailWord_453347
  simp only [CollatzResearch.WordTrace]
  refine ⟨16534923488608719348550295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11023282325739146232366863 16534923488608719348550295)
  ·
    refine ⟨24802385232913079022825443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16534923488608719348550295 24802385232913079022825443)
    ·
      refine ⟨37203577849369618534238165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24802385232913079022825443 37203577849369618534238165)
      ·
        refine ⟨871958855844600434396207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 37203577849369618534238165 871958855844600434396207)
        ·
          refine ⟨1307938283766900651594311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 871958855844600434396207 1307938283766900651594311)
          ·
            refine ⟨1961907425650350977391467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1307938283766900651594311 1961907425650350977391467)
            ·
              refine ⟨2942861138475526466087201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1961907425650350977391467 2942861138475526466087201)
              ·
                refine ⟨2207145853856644849565401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2942861138475526466087201 2207145853856644849565401)
                ·
                  refine ⟨1655359390392483637174051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2207145853856644849565401 1655359390392483637174051)
                  ·
                    refine ⟨2483039085588725455761077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1655359390392483637174051 2483039085588725455761077)
                    ·
                      refine ⟨232784914273943011477601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2483039085588725455761077 232784914273943011477601)
                      ·
                        rfl

theorem cell23_453347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_453347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_453347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_453347 prefixEnd_453347 := by exact prefixLift 453347
  have htrace : WordTrace (prefixWord ++ tailWord_453347) baseStart_453347 baseEnd_453347 := by
    simpa [prefixWord, tailWord_453347, baseEnd_453347] using wordTrace_append hprefix tailTrace_453347
  have hstable : (prefixWord ++ tailWord_453347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453347).length < 2 ^ (prefixWord ++ tailWord_453347).sum := by decide
  have hdescent : baseEnd_453347 < baseStart_453347 := by decide
  rcases family_descends (prefixWord ++ tailWord_453347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453367 : List Nat := [1, 1, 3, 1, 1, 1, 3, 7, 5]
def baseStart_453367 : Nat := 118140960795 + 453367 * 2 ^ 59
def prefixEnd_453367 : Nat := 4983230072969 + 3 ^ 40 * 453367 * 2
def baseEnd_453367 : Nat := 25866131543003659247501

theorem tailTrace_453367 : CollatzResearch.WordTrace tailWord_453367 prefixEnd_453367 25866131543003659247501 := by
  unfold tailWord_453367
  simp only [CollatzResearch.WordTrace]
  refine ⟨16535652948536262764278355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11023768632357508509518903 16535652948536262764278355)
  ·
    refine ⟨24803479422804394146417533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16535652948536262764278355 24803479422804394146417533)
    ·
      refine ⟨9301304783551647804906575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24803479422804394146417533 9301304783551647804906575)
      ·
        refine ⟨13951957175327471707359863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9301304783551647804906575 13951957175327471707359863)
        ·
          refine ⟨20927935762991207561039795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13951957175327471707359863 20927935762991207561039795)
          ·
            refine ⟨31391903644486811341559693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20927935762991207561039795 31391903644486811341559693)
            ·
              refine ⟨11771963866682554253084885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31391903644486811341559693 11771963866682554253084885)
              ·
                refine ⟨275905403125372365306677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 11771963866682554253084885 275905403125372365306677)
                ·
                  refine ⟨25866131543003659247501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 275905403125372365306677 25866131543003659247501)
                  ·
                    rfl

theorem cell23_453367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 7, 5].length) (baseStart_453367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_453367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_453367 prefixEnd_453367 := by exact prefixLift 453367
  have htrace : WordTrace (prefixWord ++ tailWord_453367) baseStart_453367 baseEnd_453367 := by
    simpa [prefixWord, tailWord_453367, baseEnd_453367] using wordTrace_append hprefix tailTrace_453367
  have hstable : (prefixWord ++ tailWord_453367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453367).length < 2 ^ (prefixWord ++ tailWord_453367).sum := by decide
  have hdescent : baseEnd_453367 < baseStart_453367 := by decide
  rcases family_descends (prefixWord ++ tailWord_453367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453377 : List Nat := [1, 2, 4, 1, 1, 1, 1, 4, 2, 3, 3]
def baseStart_453377 : Nat := 118140960795 + 453377 * 2 ^ 59
def prefixEnd_453377 : Nat := 4983230072969 + 3 ^ 40 * 453377 * 2
def baseEnd_453377 : Nat := 232800318693577894102463

theorem tailTrace_453377 : CollatzResearch.WordTrace tailWord_453377 prefixEnd_453377 232800318693577894102463 := by
  unfold tailWord_453377
  simp only [CollatzResearch.WordTrace]
  refine ⟨16536017678500034472142385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11024011785666689648094923 16536017678500034472142385)
  ·
    refine ⟨12402013258875025854106789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16536017678500034472142385 12402013258875025854106789)
    ·
      refine ⟨2325377486039067347645023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12402013258875025854106789 2325377486039067347645023)
      ·
        refine ⟨3488066229058601021467535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2325377486039067347645023 3488066229058601021467535)
        ·
          refine ⟨5232099343587901532201303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3488066229058601021467535 5232099343587901532201303)
          ·
            refine ⟨7848149015381852298301955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5232099343587901532201303 7848149015381852298301955)
            ·
              refine ⟨11772223523072778447452933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7848149015381852298301955 11772223523072778447452933)
              ·
                refine ⟨2207291910576145958897425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11772223523072778447452933 2207291910576145958897425)
                ·
                  refine ⟨1655468932932109469173069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2207291910576145958897425 1655468932932109469173069)
                  ·
                    refine ⟨620800849849541050939901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1655468932932109469173069 620800849849541050939901)
                    ·
                      refine ⟨232800318693577894102463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 620800849849541050939901 232800318693577894102463)
                      ·
                        rfl

theorem cell23_453377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_453377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_453377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_453377 prefixEnd_453377 := by exact prefixLift 453377
  have htrace : WordTrace (prefixWord ++ tailWord_453377) baseStart_453377 baseEnd_453377 := by
    simpa [prefixWord, tailWord_453377, baseEnd_453377] using wordTrace_append hprefix tailTrace_453377
  have hstable : (prefixWord ++ tailWord_453377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453377).length < 2 ^ (prefixWord ++ tailWord_453377).sum := by decide
  have hdescent : baseEnd_453377 < baseStart_453377 := by decide
  rcases family_descends (prefixWord ++ tailWord_453377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453378 : List Nat := [3, 4, 1, 1, 1, 2, 1, 4, 2, 2, 2]
def baseStart_453378 : Nat := 118140960795 + 453378 * 2 ^ 59
def prefixEnd_453378 : Nat := 4983230072969 + 3 ^ 40 * 453378 * 2
def baseEnd_453378 : Nat := 232800832174232390189959

theorem tailTrace_453378 : CollatzResearch.WordTrace tailWord_453378 prefixEnd_453378 232800832174232390189959 := by
  unfold tailWord_453378
  simp only [CollatzResearch.WordTrace]
  refine ⟨4134013537874102910732197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11024036100997607761952525 4134013537874102910732197)
  ·
    refine ⟨775127538351394295762287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4134013537874102910732197 775127538351394295762287)
    ·
      refine ⟨1162691307527091443643431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 775127538351394295762287 1162691307527091443643431)
      ·
        refine ⟨1744036961290637165465147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1162691307527091443643431 1744036961290637165465147)
        ·
          refine ⟨2616055441935955748197721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1744036961290637165465147 2616055441935955748197721)
          ·
            refine ⟨1962041581451966811148291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2616055441935955748197721 1962041581451966811148291)
            ·
              refine ⟨2943062372177950216722437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1962041581451966811148291 2943062372177950216722437)
              ·
                refine ⟨551824194783365665635457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2943062372177950216722437 551824194783365665635457)
                ·
                  refine ⟨413868146087524249226593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 551824194783365665635457 413868146087524249226593)
                  ·
                    refine ⟨310401109565643186919945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 413868146087524249226593 310401109565643186919945)
                    ·
                      refine ⟨232800832174232390189959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 310401109565643186919945 232800832174232390189959)
                      ·
                        rfl

theorem cell23_453378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_453378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_453378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_453378 prefixEnd_453378 := by exact prefixLift 453378
  have htrace : WordTrace (prefixWord ++ tailWord_453378) baseStart_453378 baseEnd_453378 := by
    simpa [prefixWord, tailWord_453378, baseEnd_453378] using wordTrace_append hprefix tailTrace_453378
  have hstable : (prefixWord ++ tailWord_453378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453378).length < 2 ^ (prefixWord ++ tailWord_453378).sum := by decide
  have hdescent : baseEnd_453378 < baseStart_453378 := by decide
  rcases family_descends (prefixWord ++ tailWord_453378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453384 : List Nat := [2, 1, 3, 2, 2, 3, 1, 4, 5]
def baseStart_453384 : Nat := 118140960795 + 453384 * 2 ^ 59
def prefixEnd_453384 : Nat := 4983230072969 + 3 ^ 40 * 453384 * 2
def baseEnd_453384 : Nat := 25867101450906596301659

theorem tailTrace_453384 : CollatzResearch.WordTrace tailWord_453384 prefixEnd_453384 25867101450906596301659 := by
  unfold tailWord_453384
  simp only [CollatzResearch.WordTrace]
  refine ⟨8268136494737337333823603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11024181992983116445098137 8268136494737337333823603)
  ·
    refine ⟨12402204742106006000735405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8268136494737337333823603 12402204742106006000735405)
    ·
      refine ⟨4650826778289752250275777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12402204742106006000735405 4650826778289752250275777)
      ·
        refine ⟨3488120083717314187706833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4650826778289752250275777 3488120083717314187706833)
        ·
          refine ⟨2616090062787985640780125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3488120083717314187706833 2616090062787985640780125)
          ·
            refine ⟨981033773545494615292547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2616090062787985640780125 981033773545494615292547)
            ·
              refine ⟨1471550660318241922938821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 981033773545494615292547 1471550660318241922938821)
              ·
                refine ⟨275915748809670360551029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1471550660318241922938821 275915748809670360551029)
                ·
                  refine ⟨25867101450906596301659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 275915748809670360551029 25867101450906596301659)
                  ·
                    rfl

theorem cell23_453384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 4, 5].length) (baseStart_453384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_453384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_453384 prefixEnd_453384 := by exact prefixLift 453384
  have htrace : WordTrace (prefixWord ++ tailWord_453384) baseStart_453384 baseEnd_453384 := by
    simpa [prefixWord, tailWord_453384, baseEnd_453384] using wordTrace_append hprefix tailTrace_453384
  have hstable : (prefixWord ++ tailWord_453384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453384).length < 2 ^ (prefixWord ++ tailWord_453384).sum := by decide
  have hdescent : baseEnd_453384 < baseStart_453384 := by decide
  rcases family_descends (prefixWord ++ tailWord_453384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453418 : List Nat := [3, 1, 4, 3, 1, 1, 2, 3, 5]
def baseStart_453418 : Nat := 118140960795 + 453418 * 2 ^ 59
def prefixEnd_453418 : Nat := 4983230072969 + 3 ^ 40 * 453418 * 2
def baseEnd_453418 : Nat := 25869041266712470409975

theorem tailTrace_453418 : CollatzResearch.WordTrace tailWord_453418 prefixEnd_453418 25869041266712470409975 := by
  unfold tailWord_453418
  simp only [CollatzResearch.WordTrace]
  refine ⟨4134378267837874618596227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11025008714234332316256605 4134378267837874618596227)
  ·
    refine ⟨6201567401756811927894341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4134378267837874618596227 6201567401756811927894341)
    ·
      refine ⟨1162793887829402236480189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6201567401756811927894341 1162793887829402236480189)
      ·
        refine ⟨436047707936025838680071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1162793887829402236480189 436047707936025838680071)
        ·
          refine ⟨654071561904038758020107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436047707936025838680071 654071561904038758020107)
          ·
            refine ⟨981107342856058137030161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 654071561904038758020107 981107342856058137030161)
            ·
              refine ⟨735830507142043602772621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 981107342856058137030161 735830507142043602772621)
              ·
                refine ⟨275936440178266351039733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 735830507142043602772621 275936440178266351039733)
                ·
                  refine ⟨25869041266712470409975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 275936440178266351039733 25869041266712470409975)
                  ·
                    rfl

theorem cell23_453418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 3, 5].length) (baseStart_453418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_453418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_453418 prefixEnd_453418 := by exact prefixLift 453418
  have htrace : WordTrace (prefixWord ++ tailWord_453418) baseStart_453418 baseEnd_453418 := by
    simpa [prefixWord, tailWord_453418, baseEnd_453418] using wordTrace_append hprefix tailTrace_453418
  have hstable : (prefixWord ++ tailWord_453418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453418).length < 2 ^ (prefixWord ++ tailWord_453418).sum := by decide
  have hdescent : baseEnd_453418 < baseStart_453418 := by decide
  rcases family_descends (prefixWord ++ tailWord_453418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453501 : List Nat := [1, 4, 1, 1, 2, 1, 5, 1, 3, 1, 3]
def baseStart_453501 : Nat := 118140960795 + 453501 * 2 ^ 59
def prefixEnd_453501 : Nat := 4983230072969 + 3 ^ 40 * 453501 * 2
def baseEnd_453501 : Nat := 232863990294735408951893

theorem tailTrace_453501 : CollatzResearch.WordTrace tailWord_453501 prefixEnd_453501 232863990294735408951893 := by
  unfold tailWord_453501
  simp only [CollatzResearch.WordTrace]
  refine ⟨16540540330050803649656357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11027026886700535766437571 16540540330050803649656357)
  ·
    refine ⟨3101351311884525684310567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16540540330050803649656357 3101351311884525684310567)
    ·
      refine ⟨4652026967826788526465851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3101351311884525684310567 4652026967826788526465851)
      ·
        refine ⟨6978040451740182789698777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4652026967826788526465851 6978040451740182789698777)
        ·
          refine ⟨5233530338805137092274083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6978040451740182789698777 5233530338805137092274083)
          ·
            refine ⟨7850295508207705638411125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5233530338805137092274083 7850295508207705638411125)
            ·
              refine ⟨735965203894472403601043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7850295508207705638411125 735965203894472403601043)
              ·
                refine ⟨1103947805841708605401565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 735965203894472403601043 1103947805841708605401565)
                ·
                  refine ⟨413980427190640727025587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1103947805841708605401565 413980427190640727025587)
                  ·
                    refine ⟨620970640785961090538381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 413980427190640727025587 620970640785961090538381)
                    ·
                      refine ⟨232863990294735408951893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 620970640785961090538381 232863990294735408951893)
                      ·
                        rfl

theorem cell23_453501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 3, 1, 3].length) (baseStart_453501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_453501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_453501 prefixEnd_453501 := by exact prefixLift 453501
  have htrace : WordTrace (prefixWord ++ tailWord_453501) baseStart_453501 baseEnd_453501 := by
    simpa [prefixWord, tailWord_453501, baseEnd_453501] using wordTrace_append hprefix tailTrace_453501
  have hstable : (prefixWord ++ tailWord_453501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453501).length < 2 ^ (prefixWord ++ tailWord_453501).sum := by decide
  have hdescent : baseEnd_453501 < baseStart_453501 := by decide
  rcases family_descends (prefixWord ++ tailWord_453501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453538 : List Nat := [3, 3, 1, 2, 2, 2, 3, 1, 1, 5]
def baseStart_453538 : Nat := 118140960795 + 453538 * 2 ^ 59
def prefixEnd_453538 : Nat := 4983230072969 + 3 ^ 40 * 453538 * 2
def baseEnd_453538 : Nat := 77627663026317254729741

theorem tailTrace_453538 : CollatzResearch.WordTrace tailWord_453538 prefixEnd_453538 77627663026317254729741 := by
  unfold tailWord_453538
  simp only [CollatzResearch.WordTrace]
  refine ⟨4135472457729189742188317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11027926553944505979168845 4135472457729189742188317)
  ·
    refine ⟨1550802171648446153320619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4135472457729189742188317 1550802171648446153320619)
    ·
      refine ⟨2326203257472669229980929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1550802171648446153320619 2326203257472669229980929)
      ·
        refine ⟨1744652443104501922485697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2326203257472669229980929 1744652443104501922485697)
        ·
          refine ⟨1308489332328376441864273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1744652443104501922485697 1308489332328376441864273)
          ·
            refine ⟨981366999246282331398205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1308489332328376441864273 981366999246282331398205)
            ·
              refine ⟨368012624717355874274327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 981366999246282331398205 368012624717355874274327)
              ·
                refine ⟨552018937076033811411491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 368012624717355874274327 552018937076033811411491)
                ·
                  refine ⟨828028405614050717117237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 552018937076033811411491 828028405614050717117237)
                  ·
                    refine ⟨77627663026317254729741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 828028405614050717117237 77627663026317254729741)
                    ·
                      rfl

theorem cell23_453538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_453538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_453538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_453538 prefixEnd_453538 := by exact prefixLift 453538
  have htrace : WordTrace (prefixWord ++ tailWord_453538) baseStart_453538 baseEnd_453538 := by
    simpa [prefixWord, tailWord_453538, baseEnd_453538] using wordTrace_append hprefix tailTrace_453538
  have hstable : (prefixWord ++ tailWord_453538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453538).length < 2 ^ (prefixWord ++ tailWord_453538).sum := by decide
  have hdescent : baseEnd_453538 < baseStart_453538 := by decide
  rcases family_descends (prefixWord ++ tailWord_453538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453608 : List Nat := [2, 1, 4, 1, 1, 1, 5, 2, 2, 1, 3]
def baseStart_453608 : Nat := 118140960795 + 453608 * 2 ^ 59
def prefixEnd_453608 : Nat := 4983230072969 + 3 ^ 40 * 453608 * 2
def baseEnd_453608 : Nat := 232918932724766490313901

theorem tailTrace_453608 : CollatzResearch.WordTrace tailWord_453608 prefixEnd_453608 232918932724766490313901 := by
  unfold tailWord_453608
  simp only [CollatzResearch.WordTrace]
  refine ⟨8272221470331580461900739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11029628627108773949200985 8272221470331580461900739)
  ·
    refine ⟨12408332205497370692851109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8272221470331580461900739 12408332205497370692851109)
    ·
      refine ⟨2326562288530757004909583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12408332205497370692851109 2326562288530757004909583)
      ·
        refine ⟨3489843432796135507364375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2326562288530757004909583 3489843432796135507364375)
        ·
          refine ⟨5234765149194203261046563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3489843432796135507364375 5234765149194203261046563)
          ·
            refine ⟨7852147723791304891569845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5234765149194203261046563 7852147723791304891569845)
            ·
              refine ⟨736138849105434833584673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7852147723791304891569845 736138849105434833584673)
              ·
                refine ⟨552104136829076125188505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 736138849105434833584673 552104136829076125188505)
                ·
                  refine ⟨414078102621807093891379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 552104136829076125188505 414078102621807093891379)
                  ·
                    refine ⟨621117153932710640837069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 414078102621807093891379 621117153932710640837069)
                    ·
                      refine ⟨232918932724766490313901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 621117153932710640837069 232918932724766490313901)
                      ·
                        rfl

theorem cell23_453608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_453608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_453608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_453608 prefixEnd_453608 := by exact prefixLift 453608
  have htrace : WordTrace (prefixWord ++ tailWord_453608) baseStart_453608 baseEnd_453608 := by
    simpa [prefixWord, tailWord_453608, baseEnd_453608] using wordTrace_append hprefix tailTrace_453608
  have hstable : (prefixWord ++ tailWord_453608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453608).length < 2 ^ (prefixWord ++ tailWord_453608).sum := by decide
  have hdescent : baseEnd_453608 < baseStart_453608 := by decide
  rcases family_descends (prefixWord ++ tailWord_453608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453731 : List Nat := [1, 1, 1, 5, 1, 1, 1, 5, 3, 4]
def baseStart_453731 : Nat := 118140960795 + 453731 * 2 ^ 59
def prefixEnd_453731 : Nat := 4983230072969 + 3 ^ 40 * 453731 * 2
def baseEnd_453731 : Nat := 77660696948423169691945

theorem tailTrace_453731 : CollatzResearch.WordTrace tailWord_453731 prefixEnd_453731 77660696948423169691945 := by
  unfold tailWord_453731
  simp only [CollatzResearch.WordTrace]
  refine ⟨16548929119217552930529047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11032619412811701953686031 16548929119217552930529047)
  ·
    refine ⟨24823393678826329395793571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16548929119217552930529047 24823393678826329395793571)
    ·
      refine ⟨37235090518239494093690357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24823393678826329395793571 37235090518239494093690357)
      ·
        refine ⟨3490789736084952571283471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37235090518239494093690357 3490789736084952571283471)
        ·
          refine ⟨5236184604127428856925207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3490789736084952571283471 5236184604127428856925207)
          ·
            refine ⟨7854276906191143285387811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5236184604127428856925207 7854276906191143285387811)
            ·
              refine ⟨11781415359286714928081717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7854276906191143285387811 11781415359286714928081717)
              ·
                refine ⟨1104507689933129524507661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11781415359286714928081717 1104507689933129524507661)
                ·
                  refine ⟨414190383724923571690373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1104507689933129524507661 414190383724923571690373)
                  ·
                    refine ⟨77660696948423169691945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 414190383724923571690373 77660696948423169691945)
                    ·
                      rfl

theorem cell23_453731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 3, 4].length) (baseStart_453731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_453731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_453731 prefixEnd_453731 := by exact prefixLift 453731
  have htrace : WordTrace (prefixWord ++ tailWord_453731) baseStart_453731 baseEnd_453731 := by
    simpa [prefixWord, tailWord_453731, baseEnd_453731] using wordTrace_append hprefix tailTrace_453731
  have hstable : (prefixWord ++ tailWord_453731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453731).length < 2 ^ (prefixWord ++ tailWord_453731).sum := by decide
  have hdescent : baseEnd_453731 < baseStart_453731 := by decide
  rcases family_descends (prefixWord ++ tailWord_453731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453738 : List Nat := [3, 1, 3, 2, 2, 1, 1, 1, 1, 6, 2]
def baseStart_453738 : Nat := 118140960795 + 453738 * 2 ^ 59
def prefixEnd_453738 : Nat := 4983230072969 + 3 ^ 40 * 453738 * 2
def baseEnd_453738 : Nat := 232985685209850981688303

theorem tailTrace_453738 : CollatzResearch.WordTrace tailWord_453738 prefixEnd_453738 232985685209850981688303 := by
  unfold tailWord_453738
  simp only [CollatzResearch.WordTrace]
  refine ⟨4137296107548048281508467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11032789620128128750689245 4137296107548048281508467)
  ·
    refine ⟨6205944161322072422262701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4137296107548048281508467 6205944161322072422262701)
    ·
      refine ⟨2327229060495777158348513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6205944161322072422262701 2327229060495777158348513)
      ·
        refine ⟨1745421795371832868761385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2327229060495777158348513 1745421795371832868761385)
        ·
          refine ⟨1309066346528874651571039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1745421795371832868761385 1309066346528874651571039)
          ·
            refine ⟨1963599519793311977356559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1309066346528874651571039 1963599519793311977356559)
            ·
              refine ⟨2945399279689967966034839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1963599519793311977356559 2945399279689967966034839)
              ·
                refine ⟨4418098919534951949052259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2945399279689967966034839 4418098919534951949052259)
                ·
                  refine ⟨6627148379302427923578389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4418098919534951949052259 6627148379302427923578389)
                  ·
                    refine ⟨310647580279801308917737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6627148379302427923578389 310647580279801308917737)
                    ·
                      refine ⟨232985685209850981688303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 310647580279801308917737 232985685209850981688303)
                      ·
                        rfl

theorem cell23_453738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_453738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_453738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_453738 prefixEnd_453738 := by exact prefixLift 453738
  have htrace : WordTrace (prefixWord ++ tailWord_453738) baseStart_453738 baseEnd_453738 := by
    simpa [prefixWord, tailWord_453738, baseEnd_453738] using wordTrace_append hprefix tailTrace_453738
  have hstable : (prefixWord ++ tailWord_453738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453738).length < 2 ^ (prefixWord ++ tailWord_453738).sum := by decide
  have hdescent : baseEnd_453738 < baseStart_453738 := by decide
  rcases family_descends (prefixWord ++ tailWord_453738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453778 : List Nat := [3, 2, 3, 1, 1, 2, 3, 2, 6]
def baseStart_453778 : Nat := 118140960795 + 453778 * 2 ^ 59
def prefixEnd_453778 : Nat := 4983230072969 + 3 ^ 40 * 453778 * 2
def baseEnd_453778 : Nat := 25889580492892313909791

theorem tailTrace_453778 : CollatzResearch.WordTrace tailWord_453778 prefixEnd_453778 25889580492892313909791 := by
  unfold tailWord_453778
  simp only [CollatzResearch.WordTrace]
  refine ⟨4137660837511819989372497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11033762233364853304993325 4137660837511819989372497)
  ·
    refine ⟨3103245628133864992029373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4137660837511819989372497 3103245628133864992029373)
    ·
      refine ⟨1163717110550199372011015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3103245628133864992029373 1163717110550199372011015)
      ·
        refine ⟨1745575665825299058016523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1163717110550199372011015 1745575665825299058016523)
        ·
          refine ⟨2618363498737948587024785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1745575665825299058016523 2618363498737948587024785)
          ·
            refine ⟨1963772624053461440268589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2618363498737948587024785 1963772624053461440268589)
            ·
              refine ⟨736414734020048040100721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1963772624053461440268589 736414734020048040100721)
              ·
                refine ⟨552311050515036030075541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 736414734020048040100721 552311050515036030075541)
                ·
                  refine ⟨25889580492892313909791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 552311050515036030075541 25889580492892313909791)
                  ·
                    rfl

theorem cell23_453778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 2, 6].length) (baseStart_453778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_453778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_453778 prefixEnd_453778 := by exact prefixLift 453778
  have htrace : WordTrace (prefixWord ++ tailWord_453778) baseStart_453778 baseEnd_453778 := by
    simpa [prefixWord, tailWord_453778, baseEnd_453778] using wordTrace_append hprefix tailTrace_453778
  have hstable : (prefixWord ++ tailWord_453778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453778).length < 2 ^ (prefixWord ++ tailWord_453778).sum := by decide
  have hdescent : baseEnd_453778 < baseStart_453778 := by decide
  rcases family_descends (prefixWord ++ tailWord_453778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453811 : List Nat := [1, 1, 1, 2, 3, 2, 2, 3, 3, 1, 4]
def baseStart_453811 : Nat := 118140960795 + 453811 * 2 ^ 59
def prefixEnd_453811 : Nat := 4983230072969 + 3 ^ 40 * 453811 * 2
def baseEnd_453811 : Nat := 233023169297629196075467

theorem tailTrace_453811 : CollatzResearch.WordTrace tailWord_453811 prefixEnd_453811 233023169297629196075467 := by
  unfold tailWord_453811
  simp only [CollatzResearch.WordTrace]
  refine ⟨16551846958927726593441287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11034564639285151062294191 16551846958927726593441287)
  ·
    refine ⟨24827770438391589890161931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16551846958927726593441287 24827770438391589890161931)
    ·
      refine ⟨37241655657587384835242897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24827770438391589890161931 37241655657587384835242897)
      ·
        refine ⟨27931241743190538626432173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37241655657587384835242897 27931241743190538626432173)
        ·
          refine ⟨10474215653696451984912065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27931241743190538626432173 10474215653696451984912065)
          ·
            refine ⟨7855661740272338988684049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10474215653696451984912065 7855661740272338988684049)
            ·
              refine ⟨5891746305204254241513037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7855661740272338988684049 5891746305204254241513037)
              ·
                refine ⟨2209404864451595340567389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5891746305204254241513037 2209404864451595340567389)
                ·
                  refine ⟨828526824169348252712771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2209404864451595340567389 828526824169348252712771)
                  ·
                    refine ⟨1242790236254022379069157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 828526824169348252712771 1242790236254022379069157)
                    ·
                      refine ⟨233023169297629196075467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1242790236254022379069157 233023169297629196075467)
                      ·
                        rfl

theorem cell23_453811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 3, 1, 4].length) (baseStart_453811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_453811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_453811 prefixEnd_453811 := by exact prefixLift 453811
  have htrace : WordTrace (prefixWord ++ tailWord_453811) baseStart_453811 baseEnd_453811 := by
    simpa [prefixWord, tailWord_453811, baseEnd_453811] using wordTrace_append hprefix tailTrace_453811
  have hstable : (prefixWord ++ tailWord_453811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453811).length < 2 ^ (prefixWord ++ tailWord_453811).sum := by decide
  have hdescent : baseEnd_453811 < baseStart_453811 := by decide
  rcases family_descends (prefixWord ++ tailWord_453811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453821 : List Nat := [1, 4, 1, 2, 1, 1, 2, 4, 1, 6]
def baseStart_453821 : Nat := 118140960795 + 453821 * 2 ^ 59
def prefixEnd_453821 : Nat := 4983230072969 + 3 ^ 40 * 453821 * 2
def baseEnd_453821 : Nat := 77676101368058052316807

theorem tailTrace_453821 : CollatzResearch.WordTrace tailWord_453821 prefixEnd_453821 77676101368058052316807 := by
  unfold tailWord_453821
  simp only [CollatzResearch.WordTrace]
  refine ⟨16552211688891498301305317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11034807792594332200870211 16552211688891498301305317)
  ·
    refine ⟨3103539691667155931494747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16552211688891498301305317 3103539691667155931494747)
    ·
      refine ⟨4655309537500733897242121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3103539691667155931494747 4655309537500733897242121)
      ·
        refine ⟨3491482153125550422931591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4655309537500733897242121 3491482153125550422931591)
        ·
          refine ⟨5237223229688325634397387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3491482153125550422931591 5237223229688325634397387)
          ·
            refine ⟨7855834844532488451596081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5237223229688325634397387 7855834844532488451596081)
            ·
              refine ⟨5891876133399366338697061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7855834844532488451596081 5891876133399366338697061)
              ·
                refine ⟨1104726775012381188505699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5891876133399366338697061 1104726775012381188505699)
                ·
                  refine ⟨1657090162518571782758549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1104726775012381188505699 1657090162518571782758549)
                  ·
                    refine ⟨77676101368058052316807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1657090162518571782758549 77676101368058052316807)
                    ·
                      rfl

theorem cell23_453821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_453821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_453821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_453821 prefixEnd_453821 := by exact prefixLift 453821
  have htrace : WordTrace (prefixWord ++ tailWord_453821) baseStart_453821 baseEnd_453821 := by
    simpa [prefixWord, tailWord_453821, baseEnd_453821] using wordTrace_append hprefix tailTrace_453821
  have hstable : (prefixWord ++ tailWord_453821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453821).length < 2 ^ (prefixWord ++ tailWord_453821).sum := by decide
  have hdescent : baseEnd_453821 < baseStart_453821 := by decide
  rcases family_descends (prefixWord ++ tailWord_453821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453825 : List Nat := [1, 2, 6, 1, 1, 1, 2, 3, 1, 5]
def baseStart_453825 : Nat := 118140960795 + 453825 * 2 ^ 59
def prefixEnd_453825 : Nat := 4983230072969 + 3 ^ 40 * 453825 * 2
def baseEnd_453825 : Nat := 77676786008930713766801

theorem tailTrace_453825 : CollatzResearch.WordTrace tailWord_453825 prefixEnd_453825 77676786008930713766801 := by
  unfold tailWord_453825
  simp only [CollatzResearch.WordTrace]
  refine ⟨16552357580877006984450929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11034905053918004656300619 16552357580877006984450929)
  ·
    refine ⟨12414268185657755238338197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16552357580877006984450929 12414268185657755238338197)
    ·
      refine ⟨581918821202707276797103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12414268185657755238338197 581918821202707276797103)
      ·
        refine ⟨872878231804060915195655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 581918821202707276797103 872878231804060915195655)
        ·
          refine ⟨1309317347706091372793483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 872878231804060915195655 1309317347706091372793483)
          ·
            refine ⟨1963976021559137059190225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1309317347706091372793483 1963976021559137059190225)
            ·
              refine ⟨1472982016169352794392669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1963976021559137059190225 1472982016169352794392669)
              ·
                refine ⟨552368256063507297897251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1472982016169352794392669 552368256063507297897251)
                ·
                  refine ⟨828552384095260946845877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 552368256063507297897251 828552384095260946845877)
                  ·
                    refine ⟨77676786008930713766801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 828552384095260946845877 77676786008930713766801)
                    ·
                      rfl

theorem cell23_453825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_453825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_453825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_453825 prefixEnd_453825 := by exact prefixLift 453825
  have htrace : WordTrace (prefixWord ++ tailWord_453825) baseStart_453825 baseEnd_453825 := by
    simpa [prefixWord, tailWord_453825, baseEnd_453825] using wordTrace_append hprefix tailTrace_453825
  have hstable : (prefixWord ++ tailWord_453825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453825).length < 2 ^ (prefixWord ++ tailWord_453825).sum := by decide
  have hdescent : baseEnd_453825 < baseStart_453825 := by decide
  rcases family_descends (prefixWord ++ tailWord_453825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453855 : List Nat := [1, 1, 2, 3, 2, 1, 6, 1, 2, 4]
def baseStart_453855 : Nat := 118140960795 + 453855 * 2 ^ 59
def prefixEnd_453855 : Nat := 4983230072969 + 3 ^ 40 * 453855 * 2
def baseEnd_453855 : Nat := 77681920815475674641755

theorem tailTrace_453855 : CollatzResearch.WordTrace tailWord_453855 prefixEnd_453855 77681920815475674641755 := by
  unfold tailWord_453855
  simp only [CollatzResearch.WordTrace]
  refine ⟨16553451770768322108043019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11035634513845548072028679 16553451770768322108043019)
  ·
    refine ⟨24830177656152483162064529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16553451770768322108043019 24830177656152483162064529)
    ·
      refine ⟨18622633242114362371548397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24830177656152483162064529 18622633242114362371548397)
      ·
        refine ⟨6983487465792885889330649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18622633242114362371548397 6983487465792885889330649)
        ·
          refine ⟨5237615599344664416997987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6983487465792885889330649 5237615599344664416997987)
          ·
            refine ⟨7856423399016996625496981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5237615599344664416997987 7856423399016996625496981)
            ·
              refine ⟨368269846828921716820171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7856423399016996625496981 368269846828921716820171)
              ·
                refine ⟨552404770243382575230257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 368269846828921716820171 552404770243382575230257)
                ·
                  refine ⟨414303577682536931422693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 552404770243382575230257 414303577682536931422693)
                  ·
                    refine ⟨77681920815475674641755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 414303577682536931422693 77681920815475674641755)
                    ·
                      rfl

theorem cell23_453855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 1, 2, 4].length) (baseStart_453855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_453855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_453855 prefixEnd_453855 := by exact prefixLift 453855
  have htrace : WordTrace (prefixWord ++ tailWord_453855) baseStart_453855 baseEnd_453855 := by
    simpa [prefixWord, tailWord_453855, baseEnd_453855] using wordTrace_append hprefix tailTrace_453855
  have hstable : (prefixWord ++ tailWord_453855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453855).length < 2 ^ (prefixWord ++ tailWord_453855).sum := by decide
  have hdescent : baseEnd_453855 < baseStart_453855 := by decide
  rcases family_descends (prefixWord ++ tailWord_453855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453876 : List Nat := [2, 6, 1, 2, 1, 1, 3, 1, 1, 5]
def baseStart_453876 : Nat := 118140960795 + 453876 * 2 ^ 59
def prefixEnd_453876 : Nat := 4983230072969 + 3 ^ 40 * 453876 * 2
def baseEnd_453876 : Nat := 77685515180057147254223

theorem tailTrace_453876 : CollatzResearch.WordTrace tailWord_453876 prefixEnd_453876 77685515180057147254223 := by
  unfold tailWord_453876
  simp only [CollatzResearch.WordTrace]
  refine ⟨8277108851846121347278741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11036145135794828463038321 8277108851846121347278741)
  ·
    refine ⟨387989477430286938153691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8277108851846121347278741 387989477430286938153691)
    ·
      refine ⟨581984216145430407230537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387989477430286938153691 581984216145430407230537)
      ·
        refine ⟨436488162109072805422903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 581984216145430407230537 436488162109072805422903)
        ·
          refine ⟨654732243163609208134355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436488162109072805422903 654732243163609208134355)
          ·
            refine ⟨982098364745413812201533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 654732243163609208134355 982098364745413812201533)
            ·
              refine ⟨368286886779530179575575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 982098364745413812201533 368286886779530179575575)
              ·
                refine ⟨552430330169295269363363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 368286886779530179575575 552430330169295269363363)
                ·
                  refine ⟨828645495253942904045045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 552430330169295269363363 828645495253942904045045)
                  ·
                    refine ⟨77685515180057147254223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 828645495253942904045045 77685515180057147254223)
                    ·
                      rfl

theorem cell23_453876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_453876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_453876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_453876 prefixEnd_453876 := by exact prefixLift 453876
  have htrace : WordTrace (prefixWord ++ tailWord_453876) baseStart_453876 baseEnd_453876 := by
    simpa [prefixWord, tailWord_453876, baseEnd_453876] using wordTrace_append hprefix tailTrace_453876
  have hstable : (prefixWord ++ tailWord_453876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453876).length < 2 ^ (prefixWord ++ tailWord_453876).sum := by decide
  have hdescent : baseEnd_453876 < baseStart_453876 := by decide
  rcases family_descends (prefixWord ++ tailWord_453876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453935 : List Nat := [1, 1, 2, 1, 2, 1, 3, 4, 4, 2, 2]
def baseStart_453935 : Nat := 118140960795 + 453935 * 2 ^ 59
def prefixEnd_453935 : Nat := 4983230072969 + 3 ^ 40 * 453935 * 2
def baseEnd_453935 : Nat := 233086840898786710924897

theorem tailTrace_453935 : CollatzResearch.WordTrace tailWord_453935 prefixEnd_453935 233086840898786710924897 := by
  unfold tailWord_453935
  simp only [CollatzResearch.WordTrace]
  refine ⟨16556369610478495770955259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11037579740318997180636839 16556369610478495770955259)
  ·
    refine ⟨24834554415717743656432889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16556369610478495770955259 24834554415717743656432889)
    ·
      refine ⟨18625915811788307742324667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24834554415717743656432889 18625915811788307742324667)
      ·
        refine ⟨27938873717682461613487001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18625915811788307742324667 27938873717682461613487001)
        ·
          refine ⟨20954155288261846210115251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27938873717682461613487001 20954155288261846210115251)
          ·
            refine ⟨31431232932392769315172877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20954155288261846210115251 31431232932392769315172877)
            ·
              refine ⟨11786712349647288493189829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31431232932392769315172877 11786712349647288493189829)
              ·
                refine ⟨2210008565558866592473093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11786712349647288493189829 2210008565558866592473093)
                ·
                  refine ⟨414376606042287486088705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2210008565558866592473093 414376606042287486088705)
                  ·
                    refine ⟨310782454531715614566529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 414376606042287486088705 310782454531715614566529)
                    ·
                      refine ⟨233086840898786710924897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 310782454531715614566529 233086840898786710924897)
                      ·
                        rfl

theorem cell23_453935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 4, 2, 2].length) (baseStart_453935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_453935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_453935 prefixEnd_453935 := by exact prefixLift 453935
  have htrace : WordTrace (prefixWord ++ tailWord_453935) baseStart_453935 baseEnd_453935 := by
    simpa [prefixWord, tailWord_453935, baseEnd_453935] using wordTrace_append hprefix tailTrace_453935
  have hstable : (prefixWord ++ tailWord_453935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453935).length < 2 ^ (prefixWord ++ tailWord_453935).sum := by decide
  have hdescent : baseEnd_453935 < baseStart_453935 := by decide
  rcases family_descends (prefixWord ++ tailWord_453935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453939 : List Nat := [1, 1, 1, 2, 5, 4, 2, 1, 1, 3, 2]
def baseStart_453939 : Nat := 118140960795 + 453939 * 2 ^ 59
def prefixEnd_453939 : Nat := 4983230072969 + 3 ^ 40 * 453939 * 2
def baseEnd_453939 : Nat := 233088894821404695274879

theorem tailTrace_453939 : CollatzResearch.WordTrace tailWord_453939 prefixEnd_453939 233088894821404695274879 := by
  unfold tailWord_453939
  simp only [CollatzResearch.WordTrace]
  refine ⟨16556515502464004454100871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11037677001642669636067247 16556515502464004454100871)
  ·
    refine ⟨24834773253696006681151307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16556515502464004454100871 24834773253696006681151307)
    ·
      refine ⟨37252159880544010021726961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24834773253696006681151307 37252159880544010021726961)
      ·
        refine ⟨27939119910408007516295221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37252159880544010021726961 27939119910408007516295221)
        ·
          refine ⟨2619292491600750704652677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27939119910408007516295221 2619292491600750704652677)
          ·
            refine ⟨491117342175140757122377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2619292491600750704652677 491117342175140757122377)
            ·
              refine ⟨368338006631355567841783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 491117342175140757122377 368338006631355567841783)
              ·
                refine ⟨552507009947033351762675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 368338006631355567841783 552507009947033351762675)
                ·
                  refine ⟨828760514920550027644013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 552507009947033351762675 828760514920550027644013)
                  ·
                    refine ⟨310785193095206260366505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 828760514920550027644013 310785193095206260366505)
                    ·
                      refine ⟨233088894821404695274879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 310785193095206260366505 233088894821404695274879)
                      ·
                        rfl

theorem cell23_453939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 1, 1, 3, 2].length) (baseStart_453939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_453939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_453939 prefixEnd_453939 := by exact prefixLift 453939
  have htrace : WordTrace (prefixWord ++ tailWord_453939) baseStart_453939 baseEnd_453939 := by
    simpa [prefixWord, tailWord_453939, baseEnd_453939] using wordTrace_append hprefix tailTrace_453939
  have hstable : (prefixWord ++ tailWord_453939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453939).length < 2 ^ (prefixWord ++ tailWord_453939).sum := by decide
  have hdescent : baseEnd_453939 < baseStart_453939 := by decide
  rcases family_descends (prefixWord ++ tailWord_453939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453948 : List Nat := [2, 2, 2, 2, 1, 3, 1, 2, 2, 2, 4]
def baseStart_453948 : Nat := 118140960795 + 453948 * 2 ^ 59
def prefixEnd_453948 : Nat := 4983230072969 + 3 ^ 40 * 453948 * 2
def baseEnd_453948 : Nat := 233093516147295160062337

theorem tailTrace_453948 : CollatzResearch.WordTrace tailWord_453948 prefixEnd_453948 233093516147295160062337 := by
  unfold tailWord_453948
  simp only [CollatzResearch.WordTrace]
  refine ⟨8278421879715699495589249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11037895839620932660785665 8278421879715699495589249)
  ·
    refine ⟨6208816409786774621691937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8278421879715699495589249 6208816409786774621691937)
    ·
      refine ⟨4656612307340080966268953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6208816409786774621691937 4656612307340080966268953)
      ·
        refine ⟨3492459230505060724701715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4656612307340080966268953 3492459230505060724701715)
        ·
          refine ⟨5238688845757591087052573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3492459230505060724701715 5238688845757591087052573)
          ·
            refine ⟨1964508317159096657644715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5238688845757591087052573 1964508317159096657644715)
            ·
              refine ⟨2946762475738644986467073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1964508317159096657644715 2946762475738644986467073)
              ·
                refine ⟨2210071856803983739850305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2946762475738644986467073 2210071856803983739850305)
                ·
                  refine ⟨1657553892602987804887729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2210071856803983739850305 1657553892602987804887729)
                  ·
                    refine ⟨1243165419452240853665797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1657553892602987804887729 1243165419452240853665797)
                    ·
                      refine ⟨233093516147295160062337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1243165419452240853665797 233093516147295160062337)
                      ·
                        rfl

theorem cell23_453948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_453948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_453948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_453948 prefixEnd_453948 := by exact prefixLift 453948
  have htrace : WordTrace (prefixWord ++ tailWord_453948) baseStart_453948 baseEnd_453948 := by
    simpa [prefixWord, tailWord_453948, baseEnd_453948] using wordTrace_append hprefix tailTrace_453948
  have hstable : (prefixWord ++ tailWord_453948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453948).length < 2 ^ (prefixWord ++ tailWord_453948).sum := by decide
  have hdescent : baseEnd_453948 < baseStart_453948 := by decide
  rcases family_descends (prefixWord ++ tailWord_453948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453968 : List Nat := [2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 3]
def baseStart_453968 : Nat := 118140960795 + 453968 * 2 ^ 59
def prefixEnd_453968 : Nat := 4983230072969 + 3 ^ 40 * 453968 * 2
def baseEnd_453968 : Nat := 233103785760385081812245

theorem tailTrace_453968 : CollatzResearch.WordTrace tailWord_453968 prefixEnd_453968 233103785760385081812245 := by
  unfold tailWord_453968
  simp only [CollatzResearch.WordTrace]
  refine ⟨8278786609679471203453279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11038382146239294937937705 8278786609679471203453279)
  ·
    refine ⟨12418179914519206805179919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8278786609679471203453279 12418179914519206805179919)
    ·
      refine ⟨18627269871778810207769879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12418179914519206805179919 18627269871778810207769879)
      ·
        refine ⟨27940904807668215311654819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18627269871778810207769879 27940904807668215311654819)
        ·
          refine ⟨41911357211502322967482229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27940904807668215311654819 41911357211502322967482229)
          ·
            refine ⟨3929189738578342778201459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41911357211502322967482229 3929189738578342778201459)
            ·
              refine ⟨5893784607867514167302189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3929189738578342778201459 5893784607867514167302189)
              ·
                refine ⟨2210169227950317812738321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5893784607867514167302189 2210169227950317812738321)
                ·
                  refine ⟨1657626920962738359553741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2210169227950317812738321 1657626920962738359553741)
                  ·
                    refine ⟨621610095361026884832653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1657626920962738359553741 621610095361026884832653)
                    ·
                      refine ⟨233103785760385081812245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 621610095361026884832653 233103785760385081812245)
                      ·
                        rfl

theorem cell23_453968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 3].length) (baseStart_453968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_453968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_453968 prefixEnd_453968 := by exact prefixLift 453968
  have htrace : WordTrace (prefixWord ++ tailWord_453968) baseStart_453968 baseEnd_453968 := by
    simpa [prefixWord, tailWord_453968, baseEnd_453968] using wordTrace_append hprefix tailTrace_453968
  have hstable : (prefixWord ++ tailWord_453968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453968).length < 2 ^ (prefixWord ++ tailWord_453968).sum := by decide
  have hdescent : baseEnd_453968 < baseStart_453968 := by decide
  rcases family_descends (prefixWord ++ tailWord_453968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453969 : List Nat := [1, 2, 2, 1, 4, 1, 5, 1, 2, 2, 2]
def baseStart_453969 : Nat := 118140960795 + 453969 * 2 ^ 59
def prefixEnd_453969 : Nat := 4983230072969 + 3 ^ 40 * 453969 * 2
def baseEnd_453969 : Nat := 233104299241039577899741

theorem tailTrace_453969 : CollatzResearch.WordTrace tailWord_453969 prefixEnd_453969 233104299241039577899741 := by
  unfold tailWord_453969
  simp only [CollatzResearch.WordTrace]
  refine ⟨16557609692355319577692961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11038406461570213051795307 16557609692355319577692961)
  ·
    refine ⟨12418207269266489683269721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16557609692355319577692961 12418207269266489683269721)
    ·
      refine ⟨9313655451949867262452291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12418207269266489683269721 9313655451949867262452291)
      ·
        refine ⟨13970483177924800893678437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9313655451949867262452291 13970483177924800893678437)
        ·
          refine ⟨2619465595860900167564707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13970483177924800893678437 2619465595860900167564707)
          ·
            refine ⟨3929198393791350251347061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2619465595860900167564707 3929198393791350251347061)
            ·
              refine ⟨368362349417939086063787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3929198393791350251347061 368362349417939086063787)
              ·
                refine ⟨552543524126908629095681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 368362349417939086063787 552543524126908629095681)
                ·
                  refine ⟨414407643095181471821761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 552543524126908629095681 414407643095181471821761)
                  ·
                    refine ⟨310805732321386103866321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 414407643095181471821761 310805732321386103866321)
                    ·
                      refine ⟨233104299241039577899741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 310805732321386103866321 233104299241039577899741)
                      ·
                        rfl

theorem cell23_453969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 1, 2, 2, 2].length) (baseStart_453969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_453969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_453969 prefixEnd_453969 := by exact prefixLift 453969
  have htrace : WordTrace (prefixWord ++ tailWord_453969) baseStart_453969 baseEnd_453969 := by
    simpa [prefixWord, tailWord_453969, baseEnd_453969] using wordTrace_append hprefix tailTrace_453969
  have hstable : (prefixWord ++ tailWord_453969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453969).length < 2 ^ (prefixWord ++ tailWord_453969).sum := by decide
  have hdescent : baseEnd_453969 < baseStart_453969 := by decide
  rcases family_descends (prefixWord ++ tailWord_453969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453971 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 3, 7]
def baseStart_453971 : Nat := 118140960795 + 453971 * 2 ^ 59
def prefixEnd_453971 : Nat := 4983230072969 + 3 ^ 40 * 453971 * 2
def baseEnd_453971 : Nat := 77701775400782856691577

theorem tailTrace_453971 : CollatzResearch.WordTrace tailWord_453971 prefixEnd_453971 77701775400782856691577 := by
  unfold tailWord_453971
  simp only [CollatzResearch.WordTrace]
  refine ⟨16557682638348073919265767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11038455092232049279510511 16557682638348073919265767)
  ·
    refine ⟨24836523957522110878898651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16557682638348073919265767 24836523957522110878898651)
    ·
      refine ⟨37254785936283166318347977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24836523957522110878898651 37254785936283166318347977)
      ·
        refine ⟨27941089452212374738760983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37254785936283166318347977 27941089452212374738760983)
        ·
          refine ⟨41911634178318562108141475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27941089452212374738760983 41911634178318562108141475)
          ·
            refine ⟨62867451267477843162212213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41911634178318562108141475 62867451267477843162212213)
            ·
              refine ⟨5893823556326047796457395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62867451267477843162212213 5893823556326047796457395)
              ·
                refine ⟨8840735334489071694686093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5893823556326047796457395 8840735334489071694686093)
                ·
                  refine ⟨3315275750433401885507285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8840735334489071694686093 3315275750433401885507285)
                  ·
                    refine ⟨77701775400782856691577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3315275750433401885507285 77701775400782856691577)
                    ·
                      rfl

theorem cell23_453971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 7].length) (baseStart_453971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_453971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_453971 prefixEnd_453971 := by exact prefixLift 453971
  have htrace : WordTrace (prefixWord ++ tailWord_453971) baseStart_453971 baseEnd_453971 := by
    simpa [prefixWord, tailWord_453971, baseEnd_453971] using wordTrace_append hprefix tailTrace_453971
  have hstable : (prefixWord ++ tailWord_453971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453971).length < 2 ^ (prefixWord ++ tailWord_453971).sum := by decide
  have hdescent : baseEnd_453971 < baseStart_453971 := by decide
  rcases family_descends (prefixWord ++ tailWord_453971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453988 : List Nat := [2, 3, 1, 1, 3, 2, 2, 1, 1, 7]
def baseStart_453988 : Nat := 118140960795 + 453988 * 2 ^ 59
def prefixEnd_453988 : Nat := 4983230072969 + 3 ^ 40 * 453988 * 2
def baseEnd_453988 : Nat := 77704685124491667854051

theorem tailTrace_453988 : CollatzResearch.WordTrace tailWord_453988 prefixEnd_453988 77704685124491667854051 := by
  unfold tailWord_453988
  simp only [CollatzResearch.WordTrace]
  refine ⟨8279151339643242911317309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11038868452857657215089745 8279151339643242911317309)
  ·
    refine ⟨3104681752366216091743991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8279151339643242911317309 3104681752366216091743991)
    ·
      refine ⟨4657022628549324137615987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3104681752366216091743991 4657022628549324137615987)
      ·
        refine ⟨6985533942823986206423981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4657022628549324137615987 6985533942823986206423981)
        ·
          refine ⟨2619575228558994827408993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6985533942823986206423981 2619575228558994827408993)
          ·
            refine ⟨1964681421419246120556745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2619575228558994827408993 1964681421419246120556745)
            ·
              refine ⟨1473511066064434590417559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1964681421419246120556745 1473511066064434590417559)
              ·
                refine ⟨2210266599096651885626339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1473511066064434590417559 2210266599096651885626339)
                ·
                  refine ⟨3315399898644977828439509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2210266599096651885626339 3315399898644977828439509)
                  ·
                    refine ⟨77704685124491667854051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3315399898644977828439509 77704685124491667854051)
                    ·
                      rfl

theorem cell23_453988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_453988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_453988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_453988 prefixEnd_453988 := by exact prefixLift 453988
  have htrace : WordTrace (prefixWord ++ tailWord_453988) baseStart_453988 baseEnd_453988 := by
    simpa [prefixWord, tailWord_453988, baseEnd_453988] using wordTrace_append hprefix tailTrace_453988
  have hstable : (prefixWord ++ tailWord_453988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453988).length < 2 ^ (prefixWord ++ tailWord_453988).sum := by decide
  have hdescent : baseEnd_453988 < baseStart_453988 := by decide
  rcases family_descends (prefixWord ++ tailWord_453988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454052 : List Nat := [2, 3, 1, 2, 1, 1, 1, 7, 1, 4]
def baseStart_454052 : Nat := 118140960795 + 454052 * 2 ^ 59
def prefixEnd_454052 : Nat := 4983230072969 + 3 ^ 40 * 454052 * 2
def baseEnd_454052 : Nat := 77715639378454251053953

theorem tailTrace_454052 : CollatzResearch.WordTrace tailWord_454052 prefixEnd_454052 77715639378454251053953 := by
  unfold tailWord_454052
  simp only [CollatzResearch.WordTrace]
  refine ⟨8280318475527312376482205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11040424634036416501976273 8280318475527312376482205)
  ·
    refine ⟨3105119428322742141180827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8280318475527312376482205 3105119428322742141180827)
    ·
      refine ⟨4657679142484113211771241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3105119428322742141180827 4657679142484113211771241)
      ·
        refine ⟨3493259356863084908828431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4657679142484113211771241 3493259356863084908828431)
        ·
          refine ⟨5239889035294627363242647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3493259356863084908828431 5239889035294627363242647)
          ·
            refine ⟨7859833552941941044863971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5239889035294627363242647 7859833552941941044863971)
            ·
              refine ⟨11789750329412911567295957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7859833552941941044863971 11789750329412911567295957)
              ·
                refine ⟨276322273345615114858499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 11789750329412911567295957 276322273345615114858499)
                ·
                  refine ⟨414483410018422672287749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 276322273345615114858499 414483410018422672287749)
                  ·
                    refine ⟨77715639378454251053953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 414483410018422672287749 77715639378454251053953)
                    ·
                      rfl

theorem cell23_454052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 7, 1, 4].length) (baseStart_454052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454052 prefixEnd_454052 := by exact prefixLift 454052
  have htrace : WordTrace (prefixWord ++ tailWord_454052) baseStart_454052 baseEnd_454052 := by
    simpa [prefixWord, tailWord_454052, baseEnd_454052] using wordTrace_append hprefix tailTrace_454052
  have hstable : (prefixWord ++ tailWord_454052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454052).length < 2 ^ (prefixWord ++ tailWord_454052).sum := by decide
  have hdescent : baseEnd_454052 < baseStart_454052 := by decide
  rcases family_descends (prefixWord ++ tailWord_454052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454065 : List Nat := [1, 2, 2, 4, 1, 1, 4, 2, 6]
def baseStart_454065 : Nat := 118140960795 + 454065 * 2 ^ 59
def prefixEnd_454065 : Nat := 4983230072969 + 3 ^ 40 * 454065 * 2
def baseEnd_454065 : Nat := 25905954820430133588811

theorem tailTrace_454065 : CollatzResearch.WordTrace tailWord_454065 prefixEnd_454065 25905954820430133588811 := by
  unfold tailWord_454065
  simp only [CollatzResearch.WordTrace]
  refine ⟨16561111100007527973187649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11040740733338351982125099 16561111100007527973187649)
  ·
    refine ⟨12420833325005645979890737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16561111100007527973187649 12420833325005645979890737)
    ·
      refine ⟨9315624993754234484918053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12420833325005645979890737 9315624993754234484918053)
      ·
        refine ⟨1746679686328918965922135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9315624993754234484918053 1746679686328918965922135)
        ·
          refine ⟨2620019529493378448883203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1746679686328918965922135 2620019529493378448883203)
          ·
            refine ⟨3930029294240067673324805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2620019529493378448883203 3930029294240067673324805)
            ·
              refine ⟨736880492670012688748401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3930029294240067673324805 736880492670012688748401)
              ·
                refine ⟨552660369502509516561301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 736880492670012688748401 552660369502509516561301)
                ·
                  refine ⟨25905954820430133588811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 552660369502509516561301 25905954820430133588811)
                  ·
                    rfl

theorem cell23_454065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 2, 6].length) (baseStart_454065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454065 prefixEnd_454065 := by exact prefixLift 454065
  have htrace : WordTrace (prefixWord ++ tailWord_454065) baseStart_454065 baseEnd_454065 := by
    simpa [prefixWord, tailWord_454065, baseEnd_454065] using wordTrace_append hprefix tailTrace_454065
  have hstable : (prefixWord ++ tailWord_454065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454065).length < 2 ^ (prefixWord ++ tailWord_454065).sum := by decide
  have hdescent : baseEnd_454065 < baseStart_454065 := by decide
  rcases family_descends (prefixWord ++ tailWord_454065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454069 : List Nat := [1, 3, 3, 2, 2, 2, 1, 4, 1, 4]
def baseStart_454069 : Nat := 118140960795 + 454069 * 2 ^ 59
def prefixEnd_454069 : Nat := 4983230072969 + 3 ^ 40 * 454069 * 2
def baseEnd_454069 : Nat := 77718549102163062216427

theorem tailTrace_454069 : CollatzResearch.WordTrace tailWord_454069 prefixEnd_454069 77718549102163062216427 := by
  unfold tailWord_454069
  simp only [CollatzResearch.WordTrace]
  refine ⟨16561256991993036656333261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11040837994662024437555507 16561256991993036656333261)
  ·
    refine ⟨6210471371997388746124973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16561256991993036656333261 6210471371997388746124973)
    ·
      refine ⟨2328926764499020779796865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6210471371997388746124973 2328926764499020779796865)
      ·
        refine ⟨1746695073374265584847649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2328926764499020779796865 1746695073374265584847649)
        ·
          refine ⟨1310021305030699188635737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1746695073374265584847649 1310021305030699188635737)
          ·
            refine ⟨982515978773024391476803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1310021305030699188635737 982515978773024391476803)
            ·
              refine ⟨1473773968159536587215205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 982515978773024391476803 1473773968159536587215205)
              ·
                refine ⟨276332619029913110102851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1473773968159536587215205 276332619029913110102851)
                ·
                  refine ⟨414498928544869665154277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 276332619029913110102851 414498928544869665154277)
                  ·
                    refine ⟨77718549102163062216427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 414498928544869665154277 77718549102163062216427)
                    ·
                      rfl

theorem cell23_454069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_454069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454069 prefixEnd_454069 := by exact prefixLift 454069
  have htrace : WordTrace (prefixWord ++ tailWord_454069) baseStart_454069 baseEnd_454069 := by
    simpa [prefixWord, tailWord_454069, baseEnd_454069] using wordTrace_append hprefix tailTrace_454069
  have hstable : (prefixWord ++ tailWord_454069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454069).length < 2 ^ (prefixWord ++ tailWord_454069).sum := by decide
  have hdescent : baseEnd_454069 < baseStart_454069 := by decide
  rcases family_descends (prefixWord ++ tailWord_454069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454088 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 2, 1, 7]
def baseStart_454088 : Nat := 118140960795 + 454088 * 2 ^ 59
def prefixEnd_454088 : Nat := 4983230072969 + 3 ^ 40 * 454088 * 2
def baseEnd_454088 : Nat := 233165403438924612311693

theorem tailTrace_454088 : CollatzResearch.WordTrace tailWord_454088 prefixEnd_454088 233165403438924612311693 := by
  unfold tailWord_454088
  simp only [CollatzResearch.WordTrace]
  refine ⟨8280974989462101450637459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11041299985949468600849945 8280974989462101450637459)
  ·
    refine ⟨12421462484193152175956189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8280974989462101450637459 12421462484193152175956189)
    ·
      refine ⟨4658048431572432065983571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12421462484193152175956189 4658048431572432065983571)
      ·
        refine ⟨6987072647358648098975357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4658048431572432065983571 6987072647358648098975357)
        ·
          refine ⟨2620152242759493037115759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6987072647358648098975357 2620152242759493037115759)
          ·
            refine ⟨3930228364139239555673639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2620152242759493037115759 3930228364139239555673639)
            ·
              refine ⟨5895342546208859333510459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3930228364139239555673639 5895342546208859333510459)
              ·
                refine ⟨8843013819313289000265689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5895342546208859333510459 8843013819313289000265689)
                ·
                  refine ⟨6632260364484966750199267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8843013819313289000265689 6632260364484966750199267)
                  ·
                    refine ⟨9948390546727450125298901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6632260364484966750199267 9948390546727450125298901)
                    ·
                      refine ⟨233165403438924612311693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 9948390546727450125298901 233165403438924612311693)
                      ·
                        rfl

theorem cell23_454088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_454088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454088 prefixEnd_454088 := by exact prefixLift 454088
  have htrace : WordTrace (prefixWord ++ tailWord_454088) baseStart_454088 baseEnd_454088 := by
    simpa [prefixWord, tailWord_454088, baseEnd_454088] using wordTrace_append hprefix tailTrace_454088
  have hstable : (prefixWord ++ tailWord_454088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454088).length < 2 ^ (prefixWord ++ tailWord_454088).sum := by decide
  have hdescent : baseEnd_454088 < baseStart_454088 := by decide
  rcases family_descends (prefixWord ++ tailWord_454088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454092 : List Nat := [2, 2, 1, 4, 2, 1, 1, 1, 5, 1, 3]
def baseStart_454092 : Nat := 118140960795 + 454092 * 2 ^ 59
def prefixEnd_454092 : Nat := 4983230072969 + 3 ^ 40 * 454092 * 2
def baseEnd_454092 : Nat := 233167457361542596661675

theorem tailTrace_454092 : CollatzResearch.WordTrace tailWord_454092 prefixEnd_454092 233167457361542596661675 := by
  unfold tailWord_454092
  simp only [CollatzResearch.WordTrace]
  refine ⟨8281047935454855792210265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11041397247273141056280353 8281047935454855792210265)
  ·
    refine ⟨6210785951591141844157699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8281047935454855792210265 6210785951591141844157699)
    ·
      refine ⟨9316178927386712766236549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6210785951591141844157699 9316178927386712766236549)
      ·
        refine ⟨1746783548885008643669353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9316178927386712766236549 1746783548885008643669353)
        ·
          refine ⟨1310087661663756482752015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1746783548885008643669353 1310087661663756482752015)
          ·
            refine ⟨1965131492495634724128023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1310087661663756482752015 1965131492495634724128023)
            ·
              refine ⟨2947697238743452086192035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1965131492495634724128023 2947697238743452086192035)
              ·
                refine ⟨4421545858115178129288053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2947697238743452086192035 4421545858115178129288053)
                ·
                  refine ⟨414519924198297949620755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4421545858115178129288053 414519924198297949620755)
                  ·
                    refine ⟨621779886297446924431133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 414519924198297949620755 621779886297446924431133)
                    ·
                      refine ⟨233167457361542596661675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 621779886297446924431133 233167457361542596661675)
                      ·
                        rfl

theorem cell23_454092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_454092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454092 prefixEnd_454092 := by exact prefixLift 454092
  have htrace : WordTrace (prefixWord ++ tailWord_454092) baseStart_454092 baseEnd_454092 := by
    simpa [prefixWord, tailWord_454092, baseEnd_454092] using wordTrace_append hprefix tailTrace_454092
  have hstable : (prefixWord ++ tailWord_454092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454092).length < 2 ^ (prefixWord ++ tailWord_454092).sum := by decide
  have hdescent : baseEnd_454092 < baseStart_454092 := by decide
  rcases family_descends (prefixWord ++ tailWord_454092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454135 : List Nat := [1, 1, 3, 1, 1, 1, 1, 6, 3, 2, 3]
def baseStart_454135 : Nat := 118140960795 + 454135 * 2 ^ 59
def prefixEnd_454135 : Nat := 4983230072969 + 3 ^ 40 * 454135 * 2
def baseEnd_454135 : Nat := 233189537029685928423977

theorem tailTrace_454135 : CollatzResearch.WordTrace tailWord_454135 prefixEnd_454135 233189537029685928423977 := by
  unfold tailWord_454135
  simp only [CollatzResearch.WordTrace]
  refine ⟨16563664209753929928235859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11042442806502619952157239 16563664209753929928235859)
  ·
    refine ⟨24845496314630894892353789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16563664209753929928235859 24845496314630894892353789)
    ·
      refine ⟨9317061117986585584632671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24845496314630894892353789 9317061117986585584632671)
      ·
        refine ⟨13975591676979878376949007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9317061117986585584632671 13975591676979878376949007)
        ·
          refine ⟨20963387515469817565423511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13975591676979878376949007 20963387515469817565423511)
          ·
            refine ⟨31445081273204726348135267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20963387515469817565423511 31445081273204726348135267)
            ·
              refine ⟨47167621909807089522202901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31445081273204726348135267 47167621909807089522202901)
              ·
                refine ⟨2210982277022207321353261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47167621909807089522202901 2210982277022207321353261)
                ·
                  refine ⟨829118353883327745507473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2210982277022207321353261 829118353883327745507473)
                  ·
                    refine ⟨621838765412495809130605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 829118353883327745507473 621838765412495809130605)
                    ·
                      refine ⟨233189537029685928423977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 621838765412495809130605 233189537029685928423977)
                      ·
                        rfl

theorem cell23_454135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 3, 2, 3].length) (baseStart_454135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454135 prefixEnd_454135 := by exact prefixLift 454135
  have htrace : WordTrace (prefixWord ++ tailWord_454135) baseStart_454135 baseEnd_454135 := by
    simpa [prefixWord, tailWord_454135, baseEnd_454135] using wordTrace_append hprefix tailTrace_454135
  have hstable : (prefixWord ++ tailWord_454135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454135).length < 2 ^ (prefixWord ++ tailWord_454135).sum := by decide
  have hdescent : baseEnd_454135 < baseStart_454135 := by decide
  rcases family_descends (prefixWord ++ tailWord_454135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454138 : List Nat := [3, 1, 1, 1, 1, 2, 4, 10]
def baseStart_454138 : Nat := 118140960795 + 454138 * 2 ^ 59
def prefixEnd_454138 : Nat := 4983230072969 + 3 ^ 40 * 454138 * 2
def baseEnd_454138 : Nat := 8636706573024052469869

theorem tailTrace_454138 : CollatzResearch.WordTrace tailWord_454138 prefixEnd_454138 8636706573024052469869 := by
  unfold tailWord_454138
  simp only [CollatzResearch.WordTrace]
  refine ⟨4140943407185765360148767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11042515752495374293730045 4140943407185765360148767)
  ·
    refine ⟨6211415110778648040223151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4140943407185765360148767 6211415110778648040223151)
    ·
      refine ⟨9317122666167972060334727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6211415110778648040223151 9317122666167972060334727)
      ·
        refine ⟨13975683999251958090502091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9317122666167972060334727 13975683999251958090502091)
        ·
          refine ⟨20963525998877937135753137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13975683999251958090502091 20963525998877937135753137)
          ·
            refine ⟨15722644499158452851814853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20963525998877937135753137 15722644499158452851814853)
            ·
              refine ⟨2947995843592209909715285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15722644499158452851814853 2947995843592209909715285)
              ·
                refine ⟨8636706573024052469869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 2947995843592209909715285 8636706573024052469869)
                ·
                  rfl

theorem cell23_454138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 10].length) (baseStart_454138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454138 prefixEnd_454138 := by exact prefixLift 454138
  have htrace : WordTrace (prefixWord ++ tailWord_454138) baseStart_454138 baseEnd_454138 := by
    simpa [prefixWord, tailWord_454138, baseEnd_454138] using wordTrace_append hprefix tailTrace_454138
  have hstable : (prefixWord ++ tailWord_454138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454138).length < 2 ^ (prefixWord ++ tailWord_454138).sum := by decide
  have hdescent : baseEnd_454138 < baseStart_454138 := by decide
  rcases family_descends (prefixWord ++ tailWord_454138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454152 : List Nat := [2, 1, 3, 2, 1, 1, 3, 4, 1, 2, 3]
def baseStart_454152 : Nat := 118140960795 + 454152 * 2 ^ 59
def prefixEnd_454152 : Nat := 4983230072969 + 3 ^ 40 * 454152 * 2
def baseEnd_454152 : Nat := 233198266200812361911399

theorem tailTrace_454152 : CollatzResearch.WordTrace tailWord_454152 prefixEnd_454152 233198266200812361911399 := by
  unfold tailWord_454152
  simp only [CollatzResearch.WordTrace]
  refine ⟨8282142125346170915802355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11042856167128227887736473 8282142125346170915802355)
  ·
    refine ⟨12423213188019256373703533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8282142125346170915802355 12423213188019256373703533)
    ·
      refine ⟨4658704945507221140138825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12423213188019256373703533 4658704945507221140138825)
      ·
        refine ⟨3494028709130415855104119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4658704945507221140138825 3494028709130415855104119)
        ·
          refine ⟨5241043063695623782656179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3494028709130415855104119 5241043063695623782656179)
          ·
            refine ⟨7861564595543435673984269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5241043063695623782656179 7861564595543435673984269)
            ·
              refine ⟨2948086723328788377744101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7861564595543435673984269 2948086723328788377744101)
              ·
                refine ⟨552766260624147820827019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2948086723328788377744101 552766260624147820827019)
                ·
                  refine ⟨829149390936221731240529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 552766260624147820827019 829149390936221731240529)
                  ·
                    refine ⟨621862043202166298430397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 829149390936221731240529 621862043202166298430397)
                    ·
                      refine ⟨233198266200812361911399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 621862043202166298430397 233198266200812361911399)
                      ·
                        rfl

theorem cell23_454152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_454152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454152 prefixEnd_454152 := by exact prefixLift 454152
  have htrace : WordTrace (prefixWord ++ tailWord_454152) baseStart_454152 baseEnd_454152 := by
    simpa [prefixWord, tailWord_454152, baseEnd_454152] using wordTrace_append hprefix tailTrace_454152
  have hstable : (prefixWord ++ tailWord_454152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454152).length < 2 ^ (prefixWord ++ tailWord_454152).sum := by decide
  have hdescent : baseEnd_454152 < baseStart_454152 := by decide
  rcases family_descends (prefixWord ++ tailWord_454152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454155 : List Nat := [1, 1, 1, 1, 8, 1, 1, 9]
def baseStart_454155 : Nat := 118140960795 + 454155 * 2 ^ 59
def prefixEnd_454155 : Nat := 4983230072969 + 3 ^ 40 * 454155 * 2
def baseEnd_454155 : Nat := 8637029875658364821255

theorem tailTrace_454155 : CollatzResearch.WordTrace tailWord_454155 prefixEnd_454155 8637029875658364821255 := by
  unfold tailWord_454155
  simp only [CollatzResearch.WordTrace]
  refine ⟨16564393669681473343963919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11042929113120982229309279 16564393669681473343963919)
  ·
    refine ⟨24846590504522210015945879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16564393669681473343963919 24846590504522210015945879)
    ·
      refine ⟨37269885756783315023918819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24846590504522210015945879 37269885756783315023918819)
      ·
        refine ⟨55904828635174972535878229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37269885756783315023918819 55904828635174972535878229)
        ·
          refine ⟨655134710568456709404823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 55904828635174972535878229 655134710568456709404823)
          ·
            refine ⟨982702065852685064107235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 655134710568456709404823 982702065852685064107235)
            ·
              refine ⟨1474053098779027596160853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 982702065852685064107235 1474053098779027596160853)
              ·
                refine ⟨8637029875658364821255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1474053098779027596160853 8637029875658364821255)
                ·
                  rfl

theorem cell23_454155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 9].length) (baseStart_454155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454155 prefixEnd_454155 := by exact prefixLift 454155
  have htrace : WordTrace (prefixWord ++ tailWord_454155) baseStart_454155 baseEnd_454155 := by
    simpa [prefixWord, tailWord_454155, baseEnd_454155] using wordTrace_append hprefix tailTrace_454155
  have hstable : (prefixWord ++ tailWord_454155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454155).length < 2 ^ (prefixWord ++ tailWord_454155).sum := by decide
  have hdescent : baseEnd_454155 < baseStart_454155 := by decide
  rcases family_descends (prefixWord ++ tailWord_454155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454192 : List Nat := [2, 1, 1, 1, 2, 3, 1, 4, 3, 3, 2]
def baseStart_454192 : Nat := 118140960795 + 454192 * 2 ^ 59
def prefixEnd_454192 : Nat := 4983230072969 + 3 ^ 40 * 454192 * 2
def baseEnd_454192 : Nat := 233218805426992205411215

theorem tailTrace_454192 : CollatzResearch.WordTrace tailWord_454192 prefixEnd_454192 233218805426992205411215 := by
  unfold tailWord_454192
  simp only [CollatzResearch.WordTrace]
  refine ⟨8282871585273714331530415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11043828780364952442040553 8282871585273714331530415)
  ·
    refine ⟨12424307377910571497295623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8282871585273714331530415 12424307377910571497295623)
    ·
      refine ⟨18636461066865857245943435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12424307377910571497295623 18636461066865857245943435)
      ·
        refine ⟨27954691600298785868915153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18636461066865857245943435 27954691600298785868915153)
        ·
          refine ⟨20966018700224089401686365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27954691600298785868915153 20966018700224089401686365)
          ·
            refine ⟨7862257012584033525632387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20966018700224089401686365 7862257012584033525632387)
            ·
              refine ⟨11793385518876050288448581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7862257012584033525632387 11793385518876050288448581)
              ·
                refine ⟨2211259784789259429084109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11793385518876050288448581 2211259784789259429084109)
                ·
                  refine ⟨829222419295972285906541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2211259784789259429084109 829222419295972285906541)
                  ·
                    refine ⟨310958407235989607214953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 829222419295972285906541 310958407235989607214953)
                    ·
                      refine ⟨233218805426992205411215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 310958407235989607214953 233218805426992205411215)
                      ·
                        rfl

theorem cell23_454192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 3, 3, 2].length) (baseStart_454192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454192 prefixEnd_454192 := by exact prefixLift 454192
  have htrace : WordTrace (prefixWord ++ tailWord_454192) baseStart_454192 baseEnd_454192 := by
    simpa [prefixWord, tailWord_454192, baseEnd_454192] using wordTrace_append hprefix tailTrace_454192
  have hstable : (prefixWord ++ tailWord_454192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454192).length < 2 ^ (prefixWord ++ tailWord_454192).sum := by decide
  have hdescent : baseEnd_454192 < baseStart_454192 := by decide
  rcases family_descends (prefixWord ++ tailWord_454192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454199 : List Nat := [1, 1, 3, 1, 2, 5, 1, 3, 2, 1, 3]
def baseStart_454199 : Nat := 118140960795 + 454199 * 2 ^ 59
def prefixEnd_454199 : Nat := 4983230072969 + 3 ^ 40 * 454199 * 2
def baseEnd_454199 : Nat := 233222399791573678023683

theorem tailTrace_454199 : CollatzResearch.WordTrace tailWord_454199 prefixEnd_454199 233222399791573678023683 := by
  unfold tailWord_454199
  simp only [CollatzResearch.WordTrace]
  refine ⟨16565998481522068858565651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11043998987681379239043767 16565998481522068858565651)
  ·
    refine ⟨24848997722283103287848477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16565998481522068858565651 24848997722283103287848477)
    ·
      refine ⟨9318374145856163732943179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24848997722283103287848477 9318374145856163732943179)
      ·
        refine ⟨13977561218784245599414769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9318374145856163732943179 13977561218784245599414769)
        ·
          refine ⟨10483170914088184199561077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13977561218784245599414769 10483170914088184199561077)
          ·
            refine ⟨982797273195767268708851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10483170914088184199561077 982797273195767268708851)
            ·
              refine ⟨1474195909793650903063277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 982797273195767268708851 1474195909793650903063277)
              ·
                refine ⟨552823466172619088648729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1474195909793650903063277 552823466172619088648729)
                ·
                  refine ⟨414617599629464316486547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 552823466172619088648729 414617599629464316486547)
                  ·
                    refine ⟨621926399444196474729821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 414617599629464316486547 621926399444196474729821)
                    ·
                      refine ⟨233222399791573678023683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 621926399444196474729821 233222399791573678023683)
                      ·
                        rfl

theorem cell23_454199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 3, 2, 1, 3].length) (baseStart_454199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454199 prefixEnd_454199 := by exact prefixLift 454199
  have htrace : WordTrace (prefixWord ++ tailWord_454199) baseStart_454199 baseEnd_454199 := by
    simpa [prefixWord, tailWord_454199, baseEnd_454199] using wordTrace_append hprefix tailTrace_454199
  have hstable : (prefixWord ++ tailWord_454199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454199).length < 2 ^ (prefixWord ++ tailWord_454199).sum := by decide
  have hdescent : baseEnd_454199 < baseStart_454199 := by decide
  rcases family_descends (prefixWord ++ tailWord_454199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454209 : List Nat := [1, 2, 5, 1, 1, 1, 3, 1, 3, 3, 2]
def baseStart_454209 : Nat := 118140960795 + 454209 * 2 ^ 59
def prefixEnd_454209 : Nat := 4983230072969 + 3 ^ 40 * 454209 * 2
def baseEnd_454209 : Nat := 233227534598118638898637

theorem tailTrace_454209 : CollatzResearch.WordTrace tailWord_454209 prefixEnd_454209 233227534598118638898637 := by
  unfold tailWord_454209
  simp only [CollatzResearch.WordTrace]
  refine ⟨16566363211485840566429681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11044242140990560377619787 16566363211485840566429681)
  ·
    refine ⟨12424772408614380424822261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16566363211485840566429681 12424772408614380424822261)
    ·
      refine ⟨1164822413307598164827087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12424772408614380424822261 1164822413307598164827087)
      ·
        refine ⟨1747233619961397247240631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1164822413307598164827087 1747233619961397247240631)
        ·
          refine ⟨2620850429942095870860947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1747233619961397247240631 2620850429942095870860947)
          ·
            refine ⟨3931275644913143806291421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2620850429942095870860947 3931275644913143806291421)
            ·
              refine ⟨1474228366842428927359283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3931275644913143806291421 1474228366842428927359283)
              ·
                refine ⟨2211342550263643391038925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1474228366842428927359283 2211342550263643391038925)
                ·
                  refine ⟨829253456348866271639597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2211342550263643391038925 829253456348866271639597)
                  ·
                    refine ⟨310970046130824851864849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 829253456348866271639597 310970046130824851864849)
                    ·
                      refine ⟨233227534598118638898637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 310970046130824851864849 233227534598118638898637)
                      ·
                        rfl

theorem cell23_454209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_454209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454209 prefixEnd_454209 := by exact prefixLift 454209
  have htrace : WordTrace (prefixWord ++ tailWord_454209) baseStart_454209 baseEnd_454209 := by
    simpa [prefixWord, tailWord_454209, baseEnd_454209] using wordTrace_append hprefix tailTrace_454209
  have hstable : (prefixWord ++ tailWord_454209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454209).length < 2 ^ (prefixWord ++ tailWord_454209).sum := by decide
  have hdescent : baseEnd_454209 < baseStart_454209 := by decide
  rcases family_descends (prefixWord ++ tailWord_454209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454225 : List Nat := [1, 2, 2, 1, 3, 2, 1, 3, 2, 1, 5]
def baseStart_454225 : Nat := 118140960795 + 454225 * 2 ^ 59
def prefixEnd_454225 : Nat := 4983230072969 + 3 ^ 40 * 454225 * 2
def baseEnd_454225 : Nat := 233235750288590576298563

theorem tailTrace_454225 : CollatzResearch.WordTrace tailWord_454225 prefixEnd_454225 233235750288590576298563 := by
  unfold tailWord_454225
  simp only [CollatzResearch.WordTrace]
  refine ⟨16566946779427875299012129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11044631186285250199341419 16566946779427875299012129)
  ·
    refine ⟨12425210084570906474259097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16566946779427875299012129 12425210084570906474259097)
    ·
      refine ⟨9318907563428179855694323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12425210084570906474259097 9318907563428179855694323)
      ·
        refine ⟨13978361345142269783541485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9318907563428179855694323 13978361345142269783541485)
        ·
          refine ⟨5241885504428351168828057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13978361345142269783541485 5241885504428351168828057)
          ·
            refine ⟨3931414128321263376621043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5241885504428351168828057 3931414128321263376621043)
            ·
              refine ⟨5897121192481895064931565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3931414128321263376621043 5897121192481895064931565)
              ·
                refine ⟨2211420447180710649349337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5897121192481895064931565 2211420447180710649349337)
                ·
                  refine ⟨1658565335385532987012003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2211420447180710649349337 1658565335385532987012003)
                  ·
                    refine ⟨2487848003078299480518005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1658565335385532987012003 2487848003078299480518005)
                    ·
                      refine ⟨233235750288590576298563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2487848003078299480518005 233235750288590576298563)
                      ·
                        rfl

theorem cell23_454225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 1, 5].length) (baseStart_454225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454225 prefixEnd_454225 := by exact prefixLift 454225
  have htrace : WordTrace (prefixWord ++ tailWord_454225) baseStart_454225 baseEnd_454225 := by
    simpa [prefixWord, tailWord_454225, baseEnd_454225] using wordTrace_append hprefix tailTrace_454225
  have hstable : (prefixWord ++ tailWord_454225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454225).length < 2 ^ (prefixWord ++ tailWord_454225).sum := by decide
  have hdescent : baseEnd_454225 < baseStart_454225 := by decide
  rcases family_descends (prefixWord ++ tailWord_454225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454256 : List Nat := [2, 1, 1, 1, 6, 1, 2, 3, 2, 2, 2]
def baseStart_454256 : Nat := 118140960795 + 454256 * 2 ^ 59
def prefixEnd_454256 : Nat := 4983230072969 + 3 ^ 40 * 454256 * 2
def baseEnd_454256 : Nat := 233251668188879955010921

theorem tailTrace_454256 : CollatzResearch.WordTrace tailWord_454256 prefixEnd_454256 233251668188879955010921 := by
  unfold tailWord_454256
  simp only [CollatzResearch.WordTrace]
  refine ⟨8284038721157783796695311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11045384961543711728927081 8284038721157783796695311)
  ·
    refine ⟨12426058081736675695042967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8284038721157783796695311 12426058081736675695042967)
    ·
      refine ⟨18639087122605013542564451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12426058081736675695042967 18639087122605013542564451)
      ·
        refine ⟨27958630683907520313846677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18639087122605013542564451 27958630683907520313846677)
        ·
          refine ⟨1310560813308165014711563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 27958630683907520313846677 1310560813308165014711563)
          ·
            refine ⟨1965841219962247522067345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1310560813308165014711563 1965841219962247522067345)
            ·
              refine ⟨1474380914971685641550509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1965841219962247522067345 1474380914971685641550509)
              ·
                refine ⟨552892843114382115581441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1474380914971685641550509 552892843114382115581441)
                ·
                  refine ⟨414669632335786586686081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 552892843114382115581441 414669632335786586686081)
                  ·
                    refine ⟨311002224251839940014561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 414669632335786586686081 311002224251839940014561)
                    ·
                      refine ⟨233251668188879955010921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 311002224251839940014561 233251668188879955010921)
                      ·
                        rfl

theorem cell23_454256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 3, 2, 2, 2].length) (baseStart_454256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454256 prefixEnd_454256 := by exact prefixLift 454256
  have htrace : WordTrace (prefixWord ++ tailWord_454256) baseStart_454256 baseEnd_454256 := by
    simpa [prefixWord, tailWord_454256, baseEnd_454256] using wordTrace_append hprefix tailTrace_454256
  have hstable : (prefixWord ++ tailWord_454256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454256).length < 2 ^ (prefixWord ++ tailWord_454256).sum := by decide
  have hdescent : baseEnd_454256 < baseStart_454256 := by decide
  rcases family_descends (prefixWord ++ tailWord_454256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454262 : List Nat := [5, 1, 1, 2, 2, 1, 1, 1, 9]
def baseStart_454262 : Nat := 118140960795 + 454262 * 2 ^ 59
def prefixEnd_454262 : Nat := 4983230072969 + 3 ^ 40 * 454262 * 2
def baseEnd_454262 : Nat := 25917194341422992392877

theorem tailTrace_454262 : CollatzResearch.WordTrace tailWord_454262 prefixEnd_454262 25917194341422992392877 := by
  unfold tailWord_454262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1035518517518364413631815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11045530853529220412072693 1035518517518364413631815)
  ·
    refine ⟨1553277776277546620447723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1035518517518364413631815 1553277776277546620447723)
    ·
      refine ⟨2329916664416319930671585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1553277776277546620447723 2329916664416319930671585)
      ·
        refine ⟨1747437498312239948003689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2329916664416319930671585 1747437498312239948003689)
        ·
          refine ⟨1310578123734179961002767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1747437498312239948003689 1310578123734179961002767)
          ·
            refine ⟨1965867185601269941504151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1310578123734179961002767 1965867185601269941504151)
            ·
              refine ⟨2948800778401904912256227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1965867185601269941504151 2948800778401904912256227)
              ·
                refine ⟨4423201167602857368384341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2948800778401904912256227 4423201167602857368384341)
                ·
                  refine ⟨25917194341422992392877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4423201167602857368384341 25917194341422992392877)
                  ·
                    rfl

theorem cell23_454262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_454262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454262 prefixEnd_454262 := by exact prefixLift 454262
  have htrace : WordTrace (prefixWord ++ tailWord_454262) baseStart_454262 baseEnd_454262 := by
    simpa [prefixWord, tailWord_454262, baseEnd_454262] using wordTrace_append hprefix tailTrace_454262
  have hstable : (prefixWord ++ tailWord_454262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454262).length < 2 ^ (prefixWord ++ tailWord_454262).sum := by decide
  have hdescent : baseEnd_454262 < baseStart_454262 := by decide
  rcases family_descends (prefixWord ++ tailWord_454262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454279 : List Nat := [1, 1, 4, 2, 1, 4, 2, 3, 5]
def baseStart_454279 : Nat := 118140960795 + 454279 * 2 ^ 59
def prefixEnd_454279 : Nat := 4983230072969 + 3 ^ 40 * 454279 * 2
def baseEnd_454279 : Nat := 25918164249325929447035

theorem tailTrace_454279 : CollatzResearch.WordTrace tailWord_454279 prefixEnd_454279 25918164249325929447035 := by
  unfold tailWord_454279
  simp only [CollatzResearch.WordTrace]
  refine ⟨16568916321232242521477891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11045944214154828347651927 16568916321232242521477891)
  ·
    refine ⟨24853374481848363782216837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16568916321232242521477891 24853374481848363782216837)
    ·
      refine ⟨4660007715346568209165657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24853374481848363782216837 4660007715346568209165657)
      ·
        refine ⟨3495005786509926156874243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4660007715346568209165657 3495005786509926156874243)
        ·
          refine ⟨5242508679764889235311365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3495005786509926156874243 5242508679764889235311365)
          ·
            refine ⟨982970377455916731620881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5242508679764889235311365 982970377455916731620881)
            ·
              refine ⟨737227783091937548715661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 982970377455916731620881 737227783091937548715661)
              ·
                refine ⟨276460418659476580768373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 737227783091937548715661 276460418659476580768373)
                ·
                  refine ⟨25918164249325929447035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 276460418659476580768373 25918164249325929447035)
                  ·
                    rfl

theorem cell23_454279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 3, 5].length) (baseStart_454279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454279 prefixEnd_454279 := by exact prefixLift 454279
  have htrace : WordTrace (prefixWord ++ tailWord_454279) baseStart_454279 baseEnd_454279 := by
    simpa [prefixWord, tailWord_454279, baseEnd_454279] using wordTrace_append hprefix tailTrace_454279
  have hstable : (prefixWord ++ tailWord_454279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454279).length < 2 ^ (prefixWord ++ tailWord_454279).sum := by decide
  have hdescent : baseEnd_454279 < baseStart_454279 := by decide
  rcases family_descends (prefixWord ++ tailWord_454279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454290 : List Nat := [3, 2, 3, 1, 3, 2, 1, 2, 2, 2, 2]
def baseStart_454290 : Nat := 118140960795 + 454290 * 2 ^ 59
def prefixEnd_454290 : Nat := 4983230072969 + 3 ^ 40 * 454290 * 2
def baseEnd_454290 : Nat := 233269126531132821985765

theorem tailTrace_454290 : CollatzResearch.WordTrace tailWord_454290 prefixEnd_454290 233269126531132821985765 := by
  unfold tailWord_454290
  simp only [CollatzResearch.WordTrace]
  refine ⟨4142329381048097850032081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11046211682794927600085549 4142329381048097850032081)
  ·
    refine ⟨3106747035786073387524061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4142329381048097850032081 3106747035786073387524061)
    ·
      refine ⟨1165030138419777520321523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3106747035786073387524061 1165030138419777520321523)
      ·
        refine ⟨1747545207629666280482285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1165030138419777520321523 1747545207629666280482285)
        ·
          refine ⟨655329452861124855180857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1747545207629666280482285 655329452861124855180857)
          ·
            refine ⟨491497089645843641385643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 655329452861124855180857 491497089645843641385643)
            ·
              refine ⟨737245634468765462078465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491497089645843641385643 737245634468765462078465)
              ·
                refine ⟨552934225851574096558849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 737245634468765462078465 552934225851574096558849)
                ·
                  refine ⟨414700669388680572419137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 552934225851574096558849 414700669388680572419137)
                  ·
                    refine ⟨311025502041510429314353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 414700669388680572419137 311025502041510429314353)
                    ·
                      refine ⟨233269126531132821985765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 311025502041510429314353 233269126531132821985765)
                      ·
                        rfl

theorem cell23_454290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_454290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454290 prefixEnd_454290 := by exact prefixLift 454290
  have htrace : WordTrace (prefixWord ++ tailWord_454290) baseStart_454290 baseEnd_454290 := by
    simpa [prefixWord, tailWord_454290, baseEnd_454290] using wordTrace_append hprefix tailTrace_454290
  have hstable : (prefixWord ++ tailWord_454290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454290).length < 2 ^ (prefixWord ++ tailWord_454290).sum := by decide
  have hdescent : baseEnd_454290 < baseStart_454290 := by decide
  rcases family_descends (prefixWord ++ tailWord_454290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454335 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 10]
def baseStart_454335 : Nat := 118140960795 + 454335 * 2 ^ 59
def prefixEnd_454335 : Nat := 4983230072969 + 3 ^ 40 * 454335 * 2
def baseEnd_454335 : Nat := 25921359240065016213673

theorem tailTrace_454335 : CollatzResearch.WordTrace tailWord_454335 prefixEnd_454335 25921359240065016213673 := by
  unfold tailWord_454335
  simp only [CollatzResearch.WordTrace]
  refine ⟨16570958809029364085516459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11047305872686242723677639 16570958809029364085516459)
  ·
    refine ⟨24856438213544046128274689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16570958809029364085516459 24856438213544046128274689)
    ·
      refine ⟨18642328660158034596206017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24856438213544046128274689 18642328660158034596206017)
      ·
        refine ⟨13981746495118525947154513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18642328660158034596206017 13981746495118525947154513)
        ·
          refine ⟨10486309871338894460365885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13981746495118525947154513 10486309871338894460365885)
          ·
            refine ⟨3932366201752085422637207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10486309871338894460365885 3932366201752085422637207)
            ·
              refine ⟨5898549302628128133955811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3932366201752085422637207 5898549302628128133955811)
              ·
                refine ⟨8847823953942192200933717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5898549302628128133955811 8847823953942192200933717)
                ·
                  refine ⟨25921359240065016213673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 8847823953942192200933717 25921359240065016213673)
                  ·
                    rfl

theorem cell23_454335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 10].length) (baseStart_454335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454335 prefixEnd_454335 := by exact prefixLift 454335
  have htrace : WordTrace (prefixWord ++ tailWord_454335) baseStart_454335 baseEnd_454335 := by
    simpa [prefixWord, tailWord_454335, baseEnd_454335] using wordTrace_append hprefix tailTrace_454335
  have hstable : (prefixWord ++ tailWord_454335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454335).length < 2 ^ (prefixWord ++ tailWord_454335).sum := by decide
  have hdescent : baseEnd_454335 < baseStart_454335 := by decide
  rcases family_descends (prefixWord ++ tailWord_454335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454355 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 6]
def baseStart_454355 : Nat := 118140960795 + 454355 * 2 ^ 59
def prefixEnd_454355 : Nat := 4983230072969 + 3 ^ 40 * 454355 * 2
def baseEnd_454355 : Nat := 233302502773675067672965

theorem tailTrace_454355 : CollatzResearch.WordTrace tailWord_454355 prefixEnd_454355 233302502773675067672965 := by
  unfold tailWord_454355
  simp only [CollatzResearch.WordTrace]
  refine ⟨16571688268956907501244519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11047792179304605000829679 16571688268956907501244519)
  ·
    refine ⟨24857532403435361251866779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16571688268956907501244519 24857532403435361251866779)
    ·
      refine ⟨37286298605153041877800169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24857532403435361251866779 37286298605153041877800169)
      ·
        refine ⟨27964723953864781408350127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37286298605153041877800169 27964723953864781408350127)
        ·
          refine ⟨41947085930797172112525191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27964723953864781408350127 41947085930797172112525191)
          ·
            refine ⟨62920628896195758168787787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41947085930797172112525191 62920628896195758168787787)
            ·
              refine ⟨94380943344293637253181681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62920628896195758168787787 94380943344293637253181681)
              ·
                refine ⟨70785707508220227939886261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94380943344293637253181681 70785707508220227939886261)
                ·
                  refine ⟨6636160078895646369364337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70785707508220227939886261 6636160078895646369364337)
                  ·
                    refine ⟨4977120059171734777023253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6636160078895646369364337 4977120059171734777023253)
                    ·
                      refine ⟨233302502773675067672965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4977120059171734777023253 233302502773675067672965)
                      ·
                        rfl

theorem cell23_454355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 6].length) (baseStart_454355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454355 prefixEnd_454355 := by exact prefixLift 454355
  have htrace : WordTrace (prefixWord ++ tailWord_454355) baseStart_454355 baseEnd_454355 := by
    simpa [prefixWord, tailWord_454355, baseEnd_454355] using wordTrace_append hprefix tailTrace_454355
  have hstable : (prefixWord ++ tailWord_454355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454355).length < 2 ^ (prefixWord ++ tailWord_454355).sum := by decide
  have hdescent : baseEnd_454355 < baseStart_454355 := by decide
  rcases family_descends (prefixWord ++ tailWord_454355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454356 : List Nat := [2, 4, 1, 3, 1, 1, 3, 1, 3, 4]
def baseStart_454356 : Nat := 118140960795 + 454356 * 2 ^ 59
def prefixEnd_454356 : Nat := 4983230072969 + 3 ^ 40 * 454356 * 2
def baseEnd_454356 : Nat := 77767672084776521253487

theorem tailTrace_454356 : CollatzResearch.WordTrace tailWord_454356 prefixEnd_454356 77767672084776521253487 := by
  unfold tailWord_454356
  simp only [CollatzResearch.WordTrace]
  refine ⟨8285862370976642336015461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11047816494635523114687281 8285862370976642336015461)
  ·
    refine ⟨1553599194558120438002899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8285862370976642336015461 1553599194558120438002899)
    ·
      refine ⟨2330398791837180657004349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1553599194558120438002899 2330398791837180657004349)
      ·
        refine ⟨873899546938942746376631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2330398791837180657004349 873899546938942746376631)
        ·
          refine ⟨1310849320408414119564947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 873899546938942746376631 1310849320408414119564947)
          ·
            refine ⟨1966273980612621179347421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1310849320408414119564947 1966273980612621179347421)
            ·
              refine ⟨737352742729732942255283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1966273980612621179347421 737352742729732942255283)
              ·
                refine ⟨1106029114094599413382925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 737352742729732942255283 1106029114094599413382925)
                ·
                  refine ⟨414760917785474780018597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1106029114094599413382925 414760917785474780018597)
                  ·
                    refine ⟨77767672084776521253487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 414760917785474780018597 77767672084776521253487)
                    ·
                      rfl

theorem cell23_454356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_454356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454356 prefixEnd_454356 := by exact prefixLift 454356
  have htrace : WordTrace (prefixWord ++ tailWord_454356) baseStart_454356 baseEnd_454356 := by
    simpa [prefixWord, tailWord_454356, baseEnd_454356] using wordTrace_append hprefix tailTrace_454356
  have hstable : (prefixWord ++ tailWord_454356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454356).length < 2 ^ (prefixWord ++ tailWord_454356).sum := by decide
  have hdescent : baseEnd_454356 < baseStart_454356 := by decide
  rcases family_descends (prefixWord ++ tailWord_454356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454369 : List Nat := [1, 2, 3, 1, 5, 1, 1, 3, 6]
def baseStart_454369 : Nat := 118140960795 + 454369 * 2 ^ 59
def prefixEnd_454369 : Nat := 4983230072969 + 3 ^ 40 * 454369 * 2
def baseEnd_454369 : Nat := 25923299055870890321989

theorem tailTrace_454369 : CollatzResearch.WordTrace tailWord_454369 prefixEnd_454369 25923299055870890321989 := by
  unfold tailWord_454369
  simp only [CollatzResearch.WordTrace]
  refine ⟨16572198890906187892254161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11048132593937458594836107 16572198890906187892254161)
  ·
    refine ⟨12429149168179640919190621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16572198890906187892254161 12429149168179640919190621)
    ·
      refine ⟨4660930938067365344696483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12429149168179640919190621 4660930938067365344696483)
      ·
        refine ⟨6991396407101048017044725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4660930938067365344696483 6991396407101048017044725)
        ·
          refine ⟨655443413165723251597943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6991396407101048017044725 655443413165723251597943)
          ·
            refine ⟨983165119748584877396915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 655443413165723251597943 983165119748584877396915)
            ·
              refine ⟨1474747679622877316095373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 983165119748584877396915 1474747679622877316095373)
              ·
                refine ⟨553030379858578993535765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1474747679622877316095373 553030379858578993535765)
                ·
                  refine ⟨25923299055870890321989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 553030379858578993535765 25923299055870890321989)
                  ·
                    rfl

theorem cell23_454369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 3, 6].length) (baseStart_454369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454369 prefixEnd_454369 := by exact prefixLift 454369
  have htrace : WordTrace (prefixWord ++ tailWord_454369) baseStart_454369 baseEnd_454369 := by
    simpa [prefixWord, tailWord_454369, baseEnd_454369] using wordTrace_append hprefix tailTrace_454369
  have hstable : (prefixWord ++ tailWord_454369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454369).length < 2 ^ (prefixWord ++ tailWord_454369).sum := by decide
  have hdescent : baseEnd_454369 < baseStart_454369 := by decide
  rcases family_descends (prefixWord ++ tailWord_454369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454379 : List Nat := [1, 1, 1, 1, 2, 4, 2, 4, 3, 1, 3]
def baseStart_454379 : Nat := 118140960795 + 454379 * 2 ^ 59
def prefixEnd_454379 : Nat := 4983230072969 + 3 ^ 40 * 454379 * 2
def baseEnd_454379 : Nat := 233314826309382973772855

theorem tailTrace_454379 : CollatzResearch.WordTrace tailWord_454379 prefixEnd_454379 233314826309382973772855 := by
  unfold tailWord_454379
  simp only [CollatzResearch.WordTrace]
  refine ⟨16572563620869959600118191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11048375747246639733412127 16572563620869959600118191)
  ·
    refine ⟨24858845431304939400177287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16572563620869959600118191 24858845431304939400177287)
    ·
      refine ⟨37288268146957409100265931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24858845431304939400177287 37288268146957409100265931)
      ·
        refine ⟨55932402220436113650398897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37288268146957409100265931 55932402220436113650398897)
        ·
          refine ⟨41949301665327085237799173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55932402220436113650398897 41949301665327085237799173)
          ·
            refine ⟨7865494062248828482087345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41949301665327085237799173 7865494062248828482087345)
            ·
              refine ⟨5899120546686621361565509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7865494062248828482087345 5899120546686621361565509)
              ·
                refine ⟨1106085102503741505293533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5899120546686621361565509 1106085102503741505293533)
                ·
                  refine ⟨414781913438903064485075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1106085102503741505293533 414781913438903064485075)
                  ·
                    refine ⟨622172870158354596727613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 414781913438903064485075 622172870158354596727613)
                    ·
                      refine ⟨233314826309382973772855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 622172870158354596727613 233314826309382973772855)
                      ·
                        rfl

theorem cell23_454379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 3, 1, 3].length) (baseStart_454379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454379 prefixEnd_454379 := by exact prefixLift 454379
  have htrace : WordTrace (prefixWord ++ tailWord_454379) baseStart_454379 baseEnd_454379 := by
    simpa [prefixWord, tailWord_454379, baseEnd_454379] using wordTrace_append hprefix tailTrace_454379
  have hstable : (prefixWord ++ tailWord_454379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454379).length < 2 ^ (prefixWord ++ tailWord_454379).sum := by decide
  have hdescent : baseEnd_454379 < baseStart_454379 := by decide
  rcases family_descends (prefixWord ++ tailWord_454379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454407 : List Nat := [1, 1, 4, 4, 3, 1, 2, 2, 1, 4]
def baseStart_454407 : Nat := 118140960795 + 454407 * 2 ^ 59
def prefixEnd_454407 : Nat := 4983230072969 + 3 ^ 40 * 454407 * 2
def baseEnd_454407 : Nat := 77776401255902954740909

theorem tailTrace_454407 : CollatzResearch.WordTrace tailWord_454407 prefixEnd_454407 77776401255902954740909 := by
  unfold tailWord_454407
  simp only [CollatzResearch.WordTrace]
  refine ⟨16573584864768520382137475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11049056576512346921424983 16573584864768520382137475)
  ·
    refine ⟨24860377297152780573206213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16573584864768520382137475 24860377297152780573206213)
    ·
      refine ⟨4661320743216146357476165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24860377297152780573206213 4661320743216146357476165)
      ·
        refine ⟨873997639353027442026781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4661320743216146357476165 873997639353027442026781)
        ·
          refine ⟨327749114757385290760043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 873997639353027442026781 327749114757385290760043)
          ·
            refine ⟨491623672136077936140065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327749114757385290760043 491623672136077936140065)
            ·
              refine ⟨368717754102058452105049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 491623672136077936140065 368717754102058452105049)
              ·
                refine ⟨276538315576543839078787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 368717754102058452105049 276538315576543839078787)
                ·
                  refine ⟨414807473364815758618181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 276538315576543839078787 414807473364815758618181)
                  ·
                    refine ⟨77776401255902954740909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 414807473364815758618181 77776401255902954740909)
                    ·
                      rfl

theorem cell23_454407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 2, 1, 4].length) (baseStart_454407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454407 prefixEnd_454407 := by exact prefixLift 454407
  have htrace : WordTrace (prefixWord ++ tailWord_454407) baseStart_454407 baseEnd_454407 := by
    simpa [prefixWord, tailWord_454407, baseEnd_454407] using wordTrace_append hprefix tailTrace_454407
  have hstable : (prefixWord ++ tailWord_454407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454407).length < 2 ^ (prefixWord ++ tailWord_454407).sum := by decide
  have hdescent : baseEnd_454407 < baseStart_454407 := by decide
  rcases family_descends (prefixWord ++ tailWord_454407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454449 : List Nat := [1, 2, 2, 3, 2, 2, 2, 2, 1, 2, 4]
def baseStart_454449 : Nat := 118140960795 + 454449 * 2 ^ 59
def prefixEnd_454449 : Nat := 4983230072969 + 3 ^ 40 * 454449 * 2
def baseEnd_454449 : Nat := 233350769955197699897533

theorem tailTrace_454449 : CollatzResearch.WordTrace tailWord_454449 prefixEnd_454449 233350769955197699897533 := by
  unfold tailWord_454449
  simp only [CollatzResearch.WordTrace]
  refine ⟨16575116730616361555166401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11050077820410907703444267 16575116730616361555166401)
  ·
    refine ⟨12431337547962271166374801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16575116730616361555166401 12431337547962271166374801)
    ·
      refine ⟨9323503160971703374781101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12431337547962271166374801 9323503160971703374781101)
      ·
        refine ⟨3496313685364388765542913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9323503160971703374781101 3496313685364388765542913)
        ·
          refine ⟨2622235264023291574157185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3496313685364388765542913 2622235264023291574157185)
          ·
            refine ⟨1966676448017468680617889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2622235264023291574157185 1966676448017468680617889)
            ·
              refine ⟨1475007336013101510463417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1966676448017468680617889 1475007336013101510463417)
              ·
                refine ⟨1106255502009826132847563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1475007336013101510463417 1106255502009826132847563)
                ·
                  refine ⟨1659383253014739199271345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1106255502009826132847563 1659383253014739199271345)
                  ·
                    refine ⟨1244537439761054399453509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1659383253014739199271345 1244537439761054399453509)
                    ·
                      refine ⟨233350769955197699897533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1244537439761054399453509 233350769955197699897533)
                      ·
                        rfl

theorem cell23_454449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_454449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454449 prefixEnd_454449 := by exact prefixLift 454449
  have htrace : WordTrace (prefixWord ++ tailWord_454449) baseStart_454449 baseEnd_454449 := by
    simpa [prefixWord, tailWord_454449, baseEnd_454449] using wordTrace_append hprefix tailTrace_454449
  have hstable : (prefixWord ++ tailWord_454449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454449).length < 2 ^ (prefixWord ++ tailWord_454449).sum := by decide
  have hdescent : baseEnd_454449 < baseStart_454449 := by decide
  rcases family_descends (prefixWord ++ tailWord_454449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454456 : List Nat := [2, 1, 2, 1, 3, 4, 1, 3, 1, 2, 3]
def baseStart_454456 : Nat := 118140960795 + 454456 * 2 ^ 59
def prefixEnd_454456 : Nat := 4983230072969 + 3 ^ 40 * 454456 * 2
def baseEnd_454456 : Nat := 233354364319779172510001

theorem tailTrace_454456 : CollatzResearch.WordTrace tailWord_454456 prefixEnd_454456 233354364319779172510001 := by
  unfold tailWord_454456
  simp only [CollatzResearch.WordTrace]
  refine ⟨8287686020795500875335611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11050248027727334500447481 8287686020795500875335611)
  ·
    refine ⟨12431529031193251313003417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8287686020795500875335611 12431529031193251313003417)
    ·
      refine ⟨9323646773394938484752563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12431529031193251313003417 9323646773394938484752563)
      ·
        refine ⟨13985470160092407727128845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9323646773394938484752563 13985470160092407727128845)
        ·
          refine ⟨5244551310034652897673317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13985470160092407727128845 5244551310034652897673317)
          ·
            refine ⟨983353370631497418313747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5244551310034652897673317 983353370631497418313747)
            ·
              refine ⟨1475030055947246127470621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 983353370631497418313747 1475030055947246127470621)
              ·
                refine ⟨553136270980217297801483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1475030055947246127470621 553136270980217297801483)
                ·
                  refine ⟨829704406470325946702225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 553136270980217297801483 829704406470325946702225)
                  ·
                    refine ⟨622278304852744460026669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 829704406470325946702225 622278304852744460026669)
                    ·
                      refine ⟨233354364319779172510001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 622278304852744460026669 233354364319779172510001)
                      ·
                        rfl

theorem cell23_454456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 3, 1, 2, 3].length) (baseStart_454456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454456 prefixEnd_454456 := by exact prefixLift 454456
  have htrace : WordTrace (prefixWord ++ tailWord_454456) baseStart_454456 baseEnd_454456 := by
    simpa [prefixWord, tailWord_454456, baseEnd_454456] using wordTrace_append hprefix tailTrace_454456
  have hstable : (prefixWord ++ tailWord_454456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454456).length < 2 ^ (prefixWord ++ tailWord_454456).sum := by decide
  have hdescent : baseEnd_454456 < baseStart_454456 := by decide
  rcases family_descends (prefixWord ++ tailWord_454456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454463 : List Nat := [1, 1, 2, 2, 6, 2, 1, 2, 2, 4]
def baseStart_454463 : Nat := 118140960795 + 454463 * 2 ^ 59
def prefixEnd_454463 : Nat := 4983230072969 + 3 ^ 40 * 454463 * 2
def baseEnd_454463 : Nat := 77785986228120215040823

theorem tailTrace_454463 : CollatzResearch.WordTrace tailWord_454463 prefixEnd_454463 77785986228120215040823 := by
  unfold tailWord_454463
  simp only [CollatzResearch.WordTrace]
  refine ⟨16575627352565641946176043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11050418235043761297450695 16575627352565641946176043)
  ·
    refine ⟨24863441028848462919264065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16575627352565641946176043 24863441028848462919264065)
    ·
      refine ⟨18647580771636347189448049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24863441028848462919264065 18647580771636347189448049)
      ·
        refine ⟨13985685578727260392086037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18647580771636347189448049 13985685578727260392086037)
        ·
          refine ⟨655579011502840330879033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13985685578727260392086037 655579011502840330879033)
          ·
            refine ⟨491684258627130248159275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 655579011502840330879033 491684258627130248159275)
            ·
              refine ⟨737526387940695372238913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491684258627130248159275 737526387940695372238913)
              ·
                refine ⟨553144790955521529179185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 737526387940695372238913 553144790955521529179185)
                ·
                  refine ⟨414858593216641146884389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 553144790955521529179185 414858593216641146884389)
                  ·
                    refine ⟨77785986228120215040823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 414858593216641146884389 77785986228120215040823)
                    ·
                      rfl

theorem cell23_454463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 2, 2, 4].length) (baseStart_454463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454463 prefixEnd_454463 := by exact prefixLift 454463
  have htrace : WordTrace (prefixWord ++ tailWord_454463) baseStart_454463 baseEnd_454463 := by
    simpa [prefixWord, tailWord_454463, baseEnd_454463] using wordTrace_append hprefix tailTrace_454463
  have hstable : (prefixWord ++ tailWord_454463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454463).length < 2 ^ (prefixWord ++ tailWord_454463).sum := by decide
  have hdescent : baseEnd_454463 < baseStart_454463 := by decide
  rcases family_descends (prefixWord ++ tailWord_454463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454546 : List Nat := [3, 2, 3, 2, 1, 1, 1, 2, 2, 1, 5]
def baseStart_454546 : Nat := 118140960795 + 454546 * 2 ^ 59
def prefixEnd_454546 : Nat := 4983230072969 + 3 ^ 40 * 454546 * 2
def baseEnd_454546 : Nat := 233400577578683820384587

theorem tailTrace_454546 : CollatzResearch.WordTrace tailWord_454546 prefixEnd_454546 233400577578683820384587 := by
  unfold tailWord_454546
  simp only [CollatzResearch.WordTrace]
  refine ⟨4144663652816236780361873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11052436407509964747631661 4144663652816236780361873)
  ·
    refine ⟨3108497739612177585271405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4144663652816236780361873 3108497739612177585271405)
    ·
      refine ⟨1165686652354566594476777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3108497739612177585271405 1165686652354566594476777)
      ·
        refine ⟨874264989265924945857583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1165686652354566594476777 874264989265924945857583)
        ·
          refine ⟨1311397483898887418786375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 874264989265924945857583 1311397483898887418786375)
          ·
            refine ⟨1967096225848331128179563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1311397483898887418786375 1967096225848331128179563)
            ·
              refine ⟨2950644338772496692269345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1967096225848331128179563 2950644338772496692269345)
              ·
                refine ⟨2212983254079372519202009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2950644338772496692269345 2212983254079372519202009)
                ·
                  refine ⟨1659737440559529389401507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2212983254079372519202009 1659737440559529389401507)
                  ·
                    refine ⟨2489606160839294084102261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1659737440559529389401507 2489606160839294084102261)
                    ·
                      refine ⟨233400577578683820384587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2489606160839294084102261 233400577578683820384587)
                      ·
                        rfl

theorem cell23_454546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_454546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454546 prefixEnd_454546 := by exact prefixLift 454546
  have htrace : WordTrace (prefixWord ++ tailWord_454546) baseStart_454546 baseEnd_454546 := by
    simpa [prefixWord, tailWord_454546, baseEnd_454546] using wordTrace_append hprefix tailTrace_454546
  have hstable : (prefixWord ++ tailWord_454546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454546).length < 2 ^ (prefixWord ++ tailWord_454546).sum := by decide
  have hdescent : baseEnd_454546 < baseStart_454546 := by decide
  rcases family_descends (prefixWord ++ tailWord_454546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454579 : List Nat := [1, 1, 1, 2, 3, 1, 3, 4, 2, 5]
def baseStart_454579 : Nat := 118140960795 + 454579 * 2 ^ 59
def prefixEnd_454579 : Nat := 4983230072969 + 3 ^ 40 * 454579 * 2
def baseEnd_454579 : Nat := 77805840813427397090645

theorem tailTrace_454579 : CollatzResearch.WordTrace tailWord_454579 prefixEnd_454579 77805840813427397090645 := by
  unfold tailWord_454579
  simp only [CollatzResearch.WordTrace]
  refine ⟨16579858220145393757398791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11053238813430262504932527 16579858220145393757398791)
  ·
    refine ⟨24869787330218090636098187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16579858220145393757398791 24869787330218090636098187)
    ·
      refine ⟨37304680995327135954147281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24869787330218090636098187 37304680995327135954147281)
      ·
        refine ⟨27978510746495351965610461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37304680995327135954147281 27978510746495351965610461)
        ·
          refine ⟨10491941529935756987103923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27978510746495351965610461 10491941529935756987103923)
          ·
            refine ⟨15737912294903635480655885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10491941529935756987103923 15737912294903635480655885)
            ·
              refine ⟨5901717110588863305245957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15737912294903635480655885 5901717110588863305245957)
              ·
                refine ⟨1106571958235411869733617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5901717110588863305245957 1106571958235411869733617)
                ·
                  refine ⟨829928968676558902300213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1106571958235411869733617 829928968676558902300213)
                  ·
                    refine ⟨77805840813427397090645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 829928968676558902300213 77805840813427397090645)
                    ·
                      rfl

theorem cell23_454579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 2, 5].length) (baseStart_454579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454579 prefixEnd_454579 := by exact prefixLift 454579
  have htrace : WordTrace (prefixWord ++ tailWord_454579) baseStart_454579 baseEnd_454579 := by
    simpa [prefixWord, tailWord_454579, baseEnd_454579] using wordTrace_append hprefix tailTrace_454579
  have hstable : (prefixWord ++ tailWord_454579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454579).length < 2 ^ (prefixWord ++ tailWord_454579).sum := by decide
  have hdescent : baseEnd_454579 < baseStart_454579 := by decide
  rcases family_descends (prefixWord ++ tailWord_454579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454599 : List Nat := [1, 1, 4, 1, 1, 2, 1, 4, 1, 3, 4]
def baseStart_454599 : Nat := 118140960795 + 454599 * 2 ^ 59
def prefixEnd_454599 : Nat := 4983230072969 + 3 ^ 40 * 454599 * 2
def baseEnd_454599 : Nat := 233427792053372113021843

theorem tailTrace_454599 : CollatzResearch.WordTrace tailWord_454599 prefixEnd_454599 233427792053372113021843 := by
  unfold tailWord_454599
  simp only [CollatzResearch.WordTrace]
  refine ⟨16580587680072937173126851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11053725120048624782084567 16580587680072937173126851)
  ·
    refine ⟨24870881520109405759690277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16580587680072937173126851 24870881520109405759690277)
    ·
      refine ⟨4663290285020513579941927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24870881520109405759690277 4663290285020513579941927)
      ·
        refine ⟨6994935427530770369912891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4663290285020513579941927 6994935427530770369912891)
        ·
          refine ⟨10492403141296155554869337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6994935427530770369912891 10492403141296155554869337)
          ·
            refine ⟨7869302355972116666152003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10492403141296155554869337 7869302355972116666152003)
            ·
              refine ⟨11803953533958174999228005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7869302355972116666152003 11803953533958174999228005)
              ·
                refine ⟨2213241287617157812355251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11803953533958174999228005 2213241287617157812355251)
                ·
                  refine ⟨3319861931425736718532877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2213241287617157812355251 3319861931425736718532877)
                  ·
                    refine ⟨1244948224284651269449829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3319861931425736718532877 1244948224284651269449829)
                    ·
                      refine ⟨233427792053372113021843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1244948224284651269449829 233427792053372113021843)
                      ·
                        rfl

theorem cell23_454599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_454599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454599 prefixEnd_454599 := by exact prefixLift 454599
  have htrace : WordTrace (prefixWord ++ tailWord_454599) baseStart_454599 baseEnd_454599 := by
    simpa [prefixWord, tailWord_454599, baseEnd_454599] using wordTrace_append hprefix tailTrace_454599
  have hstable : (prefixWord ++ tailWord_454599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454599).length < 2 ^ (prefixWord ++ tailWord_454599).sum := by decide
  have hdescent : baseEnd_454599 < baseStart_454599 := by decide
  rcases family_descends (prefixWord ++ tailWord_454599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454613 : List Nat := [1, 3, 2, 3, 2, 3, 1, 1, 2, 5]
def baseStart_454613 : Nat := 118140960795 + 454613 * 2 ^ 59
def prefixEnd_454613 : Nat := 4983230072969 + 3 ^ 40 * 454613 * 2
def baseEnd_454613 : Nat := 77811660260845019415593

theorem tailTrace_454613 : CollatzResearch.WordTrace tailWord_454613 prefixEnd_454613 77811660260845019415593 := by
  unfold tailWord_454613
  simp only [CollatzResearch.WordTrace]
  refine ⟨16581098302022217564136493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11054065534681478376090995 16581098302022217564136493)
  ·
    refine ⟨6217911863258331586551185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16581098302022217564136493 6217911863258331586551185)
    ·
      refine ⟨4663433897443748689913389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6217911863258331586551185 4663433897443748689913389)
      ·
        refine ⟨1748787711541405758717521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4663433897443748689913389 1748787711541405758717521)
        ·
          refine ⟨1311590783656054319038141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1748787711541405758717521 1311590783656054319038141)
          ·
            refine ⟨491846543871020369639303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1311590783656054319038141 491846543871020369639303)
            ·
              refine ⟨737769815806530554458955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491846543871020369639303 737769815806530554458955)
              ·
                refine ⟨1106654723709795831688433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 737769815806530554458955 1106654723709795831688433)
                ·
                  refine ⟨829991042782346873766325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1106654723709795831688433 829991042782346873766325)
                  ·
                    refine ⟨77811660260845019415593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 829991042782346873766325 77811660260845019415593)
                    ·
                      rfl

theorem cell23_454613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 2, 5].length) (baseStart_454613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454613 prefixEnd_454613 := by exact prefixLift 454613
  have htrace : WordTrace (prefixWord ++ tailWord_454613) baseStart_454613 baseEnd_454613 := by
    simpa [prefixWord, tailWord_454613, baseEnd_454613] using wordTrace_append hprefix tailTrace_454613
  have hstable : (prefixWord ++ tailWord_454613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454613).length < 2 ^ (prefixWord ++ tailWord_454613).sum := by decide
  have hdescent : baseEnd_454613 < baseStart_454613 := by decide
  rcases family_descends (prefixWord ++ tailWord_454613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454616 : List Nat := [2, 1, 2, 2, 2, 2, 1, 2, 1, 6, 2]
def baseStart_454616 : Nat := 118140960795 + 454616 * 2 ^ 59
def prefixEnd_454616 : Nat := 4983230072969 + 3 ^ 40 * 454616 * 2
def baseEnd_454616 : Nat := 233436521224498546509265

theorem tailTrace_454616 : CollatzResearch.WordTrace tailWord_454616 prefixEnd_454616 233436521224498546509265 := by
  unfold tailWord_454616
  simp only [CollatzResearch.WordTrace]
  refine ⟨8290603860505674538247851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11054138480674232717663801 8290603860505674538247851)
  ·
    refine ⟨12435905790758511807371777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8290603860505674538247851 12435905790758511807371777)
    ·
      refine ⟨9326929343068883855528833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12435905790758511807371777 9326929343068883855528833)
      ·
        refine ⟨6995197007301662891646625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9326929343068883855528833 6995197007301662891646625)
        ·
          refine ⟨5246397755476247168734969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6995197007301662891646625 5246397755476247168734969)
          ·
            refine ⟨3934798316607185376551227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5246397755476247168734969 3934798316607185376551227)
            ·
              refine ⟨5902197474910778064826841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3934798316607185376551227 5902197474910778064826841)
              ·
                refine ⟨4426648106183083548620131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5902197474910778064826841 4426648106183083548620131)
                ·
                  refine ⟨6639972159274625322930197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4426648106183083548620131 6639972159274625322930197)
                  ·
                    refine ⟨311248694965998062012353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6639972159274625322930197 311248694965998062012353)
                    ·
                      refine ⟨233436521224498546509265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 311248694965998062012353 233436521224498546509265)
                      ·
                        rfl

theorem cell23_454616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 1, 6, 2].length) (baseStart_454616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454616 prefixEnd_454616 := by exact prefixLift 454616
  have htrace : WordTrace (prefixWord ++ tailWord_454616) baseStart_454616 baseEnd_454616 := by
    simpa [prefixWord, tailWord_454616, baseEnd_454616] using wordTrace_append hprefix tailTrace_454616
  have hstable : (prefixWord ++ tailWord_454616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454616).length < 2 ^ (prefixWord ++ tailWord_454616).sum := by decide
  have hdescent : baseEnd_454616 < baseStart_454616 := by decide
  rcases family_descends (prefixWord ++ tailWord_454616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454636 : List Nat := [2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 3]
def baseStart_454636 : Nat := 118140960795 + 454636 * 2 ^ 59
def prefixEnd_454636 : Nat := 4983230072969 + 3 ^ 40 * 454636 * 2
def baseEnd_454636 : Nat := 233446790837588468259173

theorem tailTrace_454636 : CollatzResearch.WordTrace tailWord_454636 prefixEnd_454636 233446790837588468259173 := by
  unfold tailWord_454636
  simp only [CollatzResearch.WordTrace]
  refine ⟨8290968590469446246111881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11054624787292594994815841 8290968590469446246111881)
  ·
    refine ⟨6218226442852084684583911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8290968590469446246111881 6218226442852084684583911)
    ·
      refine ⟨9327339664278127026875867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6218226442852084684583911 9327339664278127026875867)
      ·
        refine ⟨13991009496417190540313801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9327339664278127026875867 13991009496417190540313801)
        ·
          refine ⟨10493257122312892905235351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13991009496417190540313801 10493257122312892905235351)
          ·
            refine ⟨15739885683469339357853027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10493257122312892905235351 15739885683469339357853027)
            ·
              refine ⟨23609828525204009036779541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15739885683469339357853027 23609828525204009036779541)
              ·
                refine ⟨1106710712118937923599041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23609828525204009036779541 1106710712118937923599041)
                ·
                  refine ⟨830033034089203442699281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1106710712118937923599041 830033034089203442699281)
                  ·
                    refine ⟨622524775566902582024461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 830033034089203442699281 622524775566902582024461)
                    ·
                      refine ⟨233446790837588468259173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 622524775566902582024461 233446790837588468259173)
                      ·
                        rfl

theorem cell23_454636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 3].length) (baseStart_454636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454636 prefixEnd_454636 := by exact prefixLift 454636
  have htrace : WordTrace (prefixWord ++ tailWord_454636) baseStart_454636 baseEnd_454636 := by
    simpa [prefixWord, tailWord_454636, baseEnd_454636] using wordTrace_append hprefix tailTrace_454636
  have hstable : (prefixWord ++ tailWord_454636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454636).length < 2 ^ (prefixWord ++ tailWord_454636).sum := by decide
  have hdescent : baseEnd_454636 < baseStart_454636 := by decide
  rcases family_descends (prefixWord ++ tailWord_454636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454639 : List Nat := [1, 1, 2, 1, 4, 2, 3, 1, 8]
def baseStart_454639 : Nat := 118140960795 + 454639 * 2 ^ 59
def prefixEnd_454639 : Nat := 4983230072969 + 3 ^ 40 * 454639 * 2
def baseEnd_454639 : Nat := 25938703475505772946851

theorem tailTrace_454639 : CollatzResearch.WordTrace tailWord_454639 prefixEnd_454639 25938703475505772946851 := by
  unfold tailWord_454639
  simp only [CollatzResearch.WordTrace]
  refine ⟨16582046599928024004582971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11054697733285349336388647 16582046599928024004582971)
  ·
    refine ⟨24873069899892036006874457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16582046599928024004582971 24873069899892036006874457)
    ·
      refine ⟨18654802424919027005155843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24873069899892036006874457 18654802424919027005155843)
      ·
        refine ⟨27982203637378540507733765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18654802424919027005155843 27982203637378540507733765)
        ·
          refine ⟨5246663182008476345200081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27982203637378540507733765 5246663182008476345200081)
          ·
            refine ⟨3934997386506357258900061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5246663182008476345200081 3934997386506357258900061)
            ·
              refine ⟨1475624019939883972087523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3934997386506357258900061 1475624019939883972087523)
              ·
                refine ⟨2213436029909825958131285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1475624019939883972087523 2213436029909825958131285)
                ·
                  refine ⟨25938703475505772946851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2213436029909825958131285 25938703475505772946851)
                  ·
                    rfl

theorem cell23_454639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 8].length) (baseStart_454639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454639 prefixEnd_454639 := by exact prefixLift 454639
  have htrace : WordTrace (prefixWord ++ tailWord_454639) baseStart_454639 baseEnd_454639 := by
    simpa [prefixWord, tailWord_454639, baseEnd_454639] using wordTrace_append hprefix tailTrace_454639
  have hstable : (prefixWord ++ tailWord_454639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454639).length < 2 ^ (prefixWord ++ tailWord_454639).sum := by decide
  have hdescent : baseEnd_454639 < baseStart_454639 := by decide
  rcases family_descends (prefixWord ++ tailWord_454639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454677 : List Nat := [1, 3, 2, 1, 5, 2, 1, 3, 1, 4]
def baseStart_454677 : Nat := 118140960795 + 454677 * 2 ^ 59
def prefixEnd_454677 : Nat := 4983230072969 + 3 ^ 40 * 454677 * 2
def baseEnd_454677 : Nat := 77822614514807602615495

theorem tailTrace_454677 : CollatzResearch.WordTrace tailWord_454677 prefixEnd_454677 77822614514807602615495 := by
  unfold tailWord_454677
  simp only [CollatzResearch.WordTrace]
  refine ⟨16583432573790356494466285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11055621715860237662977523 16583432573790356494466285)
  ·
    refine ⟨6218787215171383685424857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16583432573790356494466285 6218787215171383685424857)
    ·
      refine ⟨4664090411378537764068643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6218787215171383685424857 4664090411378537764068643)
      ·
        refine ⟨6996135617067806646102965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4664090411378537764068643 6996135617067806646102965)
        ·
          refine ⟨655887714100106873072153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6996135617067806646102965 655887714100106873072153)
          ·
            refine ⟨491915785575080154804115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 655887714100106873072153 491915785575080154804115)
            ·
              refine ⟨737873678362620232206173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491915785575080154804115 737873678362620232206173)
              ·
                refine ⟨276702629385982587077315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 737873678362620232206173 276702629385982587077315)
                ·
                  refine ⟨415053944078973880615973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 276702629385982587077315 415053944078973880615973)
                  ·
                    refine ⟨77822614514807602615495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 415053944078973880615973 77822614514807602615495)
                    ·
                      rfl

theorem cell23_454677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 3, 1, 4].length) (baseStart_454677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454677 prefixEnd_454677 := by exact prefixLift 454677
  have htrace : WordTrace (prefixWord ++ tailWord_454677) baseStart_454677 baseEnd_454677 := by
    simpa [prefixWord, tailWord_454677, baseEnd_454677] using wordTrace_append hprefix tailTrace_454677
  have hstable : (prefixWord ++ tailWord_454677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454677).length < 2 ^ (prefixWord ++ tailWord_454677).sum := by decide
  have hdescent : baseEnd_454677 < baseStart_454677 := by decide
  rcases family_descends (prefixWord ++ tailWord_454677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454693 : List Nat := [1, 3, 1, 2, 2, 3, 1, 1, 4, 3, 2]
def baseStart_454693 : Nat := 118140960795 + 454693 * 2 ^ 59
def prefixEnd_454693 : Nat := 4983230072969 + 3 ^ 40 * 454693 * 2
def baseEnd_454693 : Nat := 233476059234894745246411

theorem tailTrace_454693 : CollatzResearch.WordTrace tailWord_454693 prefixEnd_454693 233476059234894745246411 := by
  unfold tailWord_454693
  simp only [CollatzResearch.WordTrace]
  refine ⟨16584016141732391227048733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11056010761154927484699155 16584016141732391227048733)
  ·
    refine ⟨6219006053149646710143275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16584016141732391227048733 6219006053149646710143275)
    ·
      refine ⟨9328509079724470065214913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6219006053149646710143275 9328509079724470065214913)
      ·
        refine ⟨6996381809793352548911185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9328509079724470065214913 6996381809793352548911185)
        ·
          refine ⟨5247286357345014411683389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6996381809793352548911185 5247286357345014411683389)
          ·
            refine ⟨1967732384004380404381271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5247286357345014411683389 1967732384004380404381271)
            ·
              refine ⟨2951598576006570606571907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1967732384004380404381271 2951598576006570606571907)
              ·
                refine ⟨4427397864009855909857861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2951598576006570606571907 4427397864009855909857861)
                ·
                  refine ⟨830137099501847983098349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4427397864009855909857861 830137099501847983098349)
                  ·
                    refine ⟨311301412313192993661881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 830137099501847983098349 311301412313192993661881)
                    ·
                      refine ⟨233476059234894745246411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 311301412313192993661881 233476059234894745246411)
                      ·
                        rfl

theorem cell23_454693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 4, 3, 2].length) (baseStart_454693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454693 prefixEnd_454693 := by exact prefixLift 454693
  have htrace : WordTrace (prefixWord ++ tailWord_454693) baseStart_454693 baseEnd_454693 := by
    simpa [prefixWord, tailWord_454693, baseEnd_454693] using wordTrace_append hprefix tailTrace_454693
  have hstable : (prefixWord ++ tailWord_454693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454693).length < 2 ^ (prefixWord ++ tailWord_454693).sum := by decide
  have hdescent : baseEnd_454693 < baseStart_454693 := by decide
  rcases family_descends (prefixWord ++ tailWord_454693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454699 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 5, 6]
def baseStart_454699 : Nat := 118140960795 + 454699 * 2 ^ 59
def prefixEnd_454699 : Nat := 4983230072969 + 3 ^ 40 * 454699 * 2
def baseEnd_454699 : Nat := 77826380039607240590461

theorem tailTrace_454699 : CollatzResearch.WordTrace tailWord_454699 prefixEnd_454699 77826380039607240590461 := by
  unfold tailWord_454699
  simp only [CollatzResearch.WordTrace]
  refine ⟨16584234979710654251767151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11056156653140436167844767 16584234979710654251767151)
  ·
    refine ⟨24876352469565981377650727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16584234979710654251767151 24876352469565981377650727)
    ·
      refine ⟨37314528704348972066476091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24876352469565981377650727 37314528704348972066476091)
      ·
        refine ⟨55971793056523458099714137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37314528704348972066476091 55971793056523458099714137)
        ·
          refine ⟨41978844792392593574785603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55971793056523458099714137 41978844792392593574785603)
          ·
            refine ⟨62968267188588890362178405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41978844792392593574785603 62968267188588890362178405)
            ·
              refine ⟨11806550097860416942908451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62968267188588890362178405 11806550097860416942908451)
              ·
                refine ⟨17709825146790625414362677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11806550097860416942908451 17709825146790625414362677)
                ·
                  refine ⟨1660296107511621132596501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17709825146790625414362677 1660296107511621132596501)
                  ·
                    refine ⟨77826380039607240590461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1660296107511621132596501 77826380039607240590461)
                    ·
                      rfl

theorem cell23_454699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 6].length) (baseStart_454699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454699 prefixEnd_454699 := by exact prefixLift 454699
  have htrace : WordTrace (prefixWord ++ tailWord_454699) baseStart_454699 baseEnd_454699 := by
    simpa [prefixWord, tailWord_454699, baseEnd_454699] using wordTrace_append hprefix tailTrace_454699
  have hstable : (prefixWord ++ tailWord_454699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454699).length < 2 ^ (prefixWord ++ tailWord_454699).sum := by decide
  have hdescent : baseEnd_454699 < baseStart_454699 := by decide
  rcases family_descends (prefixWord ++ tailWord_454699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454710 : List Nat := [5, 1, 2, 1, 1, 1, 1, 2, 4, 3, 2]
def baseStart_454710 : Nat := 118140960795 + 454710 * 2 ^ 59
def prefixEnd_454710 : Nat := 4983230072969 + 3 ^ 40 * 454710 * 2
def baseEnd_454710 : Nat := 233484788406021178733833

theorem tailTrace_454710 : CollatzResearch.WordTrace tailWord_454710 prefixEnd_454710 233484788406021178733833 := by
  unfold tailWord_454710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1036539761416925195651099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11056424121780535420278389 1036539761416925195651099)
  ·
    refine ⟨1554809642125387793476649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1036539761416925195651099 1554809642125387793476649)
    ·
      refine ⟨1166107231594040845107487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1554809642125387793476649 1166107231594040845107487)
      ·
        refine ⟨1749160847391061267661231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1166107231594040845107487 1749160847391061267661231)
        ·
          refine ⟨2623741271086591901491847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1749160847391061267661231 2623741271086591901491847)
          ·
            refine ⟨3935611906629887852237771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2623741271086591901491847 3935611906629887852237771)
            ·
              refine ⟨5903417859944831778356657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3935611906629887852237771 5903417859944831778356657)
              ·
                refine ⟨4427563394958623833767493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5903417859944831778356657 4427563394958623833767493)
                ·
                  refine ⟨830168136554741968831405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4427563394958623833767493 830168136554741968831405)
                  ·
                    refine ⟨311313051208028238311777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 830168136554741968831405 311313051208028238311777)
                    ·
                      refine ⟨233484788406021178733833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 311313051208028238311777 233484788406021178733833)
                      ·
                        rfl

theorem cell23_454710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_454710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454710 prefixEnd_454710 := by exact prefixLift 454710
  have htrace : WordTrace (prefixWord ++ tailWord_454710) baseStart_454710 baseEnd_454710 := by
    simpa [prefixWord, tailWord_454710, baseEnd_454710] using wordTrace_append hprefix tailTrace_454710
  have hstable : (prefixWord ++ tailWord_454710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454710).length < 2 ^ (prefixWord ++ tailWord_454710).sum := by decide
  have hdescent : baseEnd_454710 < baseStart_454710 := by decide
  rcases family_descends (prefixWord ++ tailWord_454710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454716 : List Nat := [2, 2, 2, 2, 2, 1, 2, 3, 1, 6]
def baseStart_454716 : Nat := 118140960795 + 454716 * 2 ^ 59
def prefixEnd_454716 : Nat := 4983230072969 + 3 ^ 40 * 454716 * 2
def baseEnd_454716 : Nat := 77829289763316051752935

theorem tailTrace_454716 : CollatzResearch.WordTrace tailWord_454716 prefixEnd_454716 77829289763316051752935 := by
  unfold tailWord_454716
  simp only [CollatzResearch.WordTrace]
  refine ⟨8292427510324533077568001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11056570013766044103424001 8292427510324533077568001)
  ·
    refine ⟨6219320632743399808176001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8292427510324533077568001 6219320632743399808176001)
    ·
      refine ⟨4664490474557549856132001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6219320632743399808176001 4664490474557549856132001)
      ·
        refine ⟨3498367855918162392099001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4664490474557549856132001 3498367855918162392099001)
        ·
          refine ⟨2623775891938621794074251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3498367855918162392099001 2623775891938621794074251)
          ·
            refine ⟨3935663837907932691111377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2623775891938621794074251 3935663837907932691111377)
            ·
              refine ⟨2951747878430949518333533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3935663837907932691111377 2951747878430949518333533)
              ·
                refine ⟨1106905454411606069375075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2951747878430949518333533 1106905454411606069375075)
                ·
                  refine ⟨1660358181617409104062613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1106905454411606069375075 1660358181617409104062613)
                  ·
                    refine ⟨77829289763316051752935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1660358181617409104062613 77829289763316051752935)
                    ·
                      rfl

theorem cell23_454716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_454716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454716 prefixEnd_454716 := by exact prefixLift 454716
  have htrace : WordTrace (prefixWord ++ tailWord_454716) baseStart_454716 baseEnd_454716 := by
    simpa [prefixWord, tailWord_454716, baseEnd_454716] using wordTrace_append hprefix tailTrace_454716
  have hstable : (prefixWord ++ tailWord_454716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454716).length < 2 ^ (prefixWord ++ tailWord_454716).sum := by decide
  have hdescent : baseEnd_454716 < baseStart_454716 := by decide
  rcases family_descends (prefixWord ++ tailWord_454716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454729 : List Nat := [1, 2, 1, 1, 2, 2, 3, 11]
def baseStart_454729 : Nat := 118140960795 + 454729 * 2 ^ 59
def prefixEnd_454729 : Nat := 4983230072969 + 3 ^ 40 * 454729 * 2
def baseEnd_454729 : Nat := 8647946094016911273935

theorem tailTrace_454729 : CollatzResearch.WordTrace tailWord_454729 prefixEnd_454729 8647946094016911273935 := by
  unfold tailWord_454729
  simp only [CollatzResearch.WordTrace]
  refine ⟨16585329169601969375359241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11056886113067979583572827 16585329169601969375359241)
  ·
    refine ⟨12438996877201477031519431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16585329169601969375359241 12438996877201477031519431)
    ·
      refine ⟨18658495315802215547279147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12438996877201477031519431 18658495315802215547279147)
      ·
        refine ⟨27987742973703323320918721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18658495315802215547279147 27987742973703323320918721)
        ·
          refine ⟨20990807230277492490689041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27987742973703323320918721 20990807230277492490689041)
          ·
            refine ⟨15743105422708119368016781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20990807230277492490689041 15743105422708119368016781)
            ·
              refine ⟨5903664533515544763006293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15743105422708119368016781 5903664533515544763006293)
              ·
                refine ⟨8647946094016911273935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 5903664533515544763006293 8647946094016911273935)
                ·
                  rfl

theorem cell23_454729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 11].length) (baseStart_454729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454729 prefixEnd_454729 := by exact prefixLift 454729
  have htrace : WordTrace (prefixWord ++ tailWord_454729) baseStart_454729 baseEnd_454729 := by
    simpa [prefixWord, tailWord_454729, baseEnd_454729] using wordTrace_append hprefix tailTrace_454729
  have hstable : (prefixWord ++ tailWord_454729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454729).length < 2 ^ (prefixWord ++ tailWord_454729).sum := by decide
  have hdescent : baseEnd_454729 < baseStart_454729 := by decide
  rcases family_descends (prefixWord ++ tailWord_454729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454733 : List Nat := [1, 6, 1, 1, 1, 1, 3, 2, 1, 6]
def baseStart_454733 : Nat := 118140960795 + 454733 * 2 ^ 59
def prefixEnd_454733 : Nat := 4983230072969 + 3 ^ 40 * 454733 * 2
def baseEnd_454733 : Nat := 77832199487024862915409

theorem tailTrace_454733 : CollatzResearch.WordTrace tailWord_454733 prefixEnd_454733 77832199487024862915409 := by
  unfold tailWord_454733
  simp only [CollatzResearch.WordTrace]
  refine ⟨16585475061587478058504853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11056983374391652039003235 16585475061587478058504853)
  ·
    refine ⟨777444143511913033992415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16585475061587478058504853 777444143511913033992415)
    ·
      refine ⟨1166166215267869550988623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 777444143511913033992415 1166166215267869550988623)
      ·
        refine ⟨1749249322901804326482935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1166166215267869550988623 1749249322901804326482935)
        ·
          refine ⟨2623873984352706489724403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1749249322901804326482935 2623873984352706489724403)
          ·
            refine ⟨3935810976529059734586605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2623873984352706489724403 3935810976529059734586605)
            ·
              refine ⟨1475929116198397400469977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3935810976529059734586605 1475929116198397400469977)
              ·
                refine ⟨1106946837148798050352483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1475929116198397400469977 1106946837148798050352483)
                ·
                  refine ⟨1660420255723197075528725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1106946837148798050352483 1660420255723197075528725)
                  ·
                    refine ⟨77832199487024862915409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1660420255723197075528725 77832199487024862915409)
                    ·
                      rfl

theorem cell23_454733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_454733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454733 prefixEnd_454733 := by exact prefixLift 454733
  have htrace : WordTrace (prefixWord ++ tailWord_454733) baseStart_454733 baseEnd_454733 := by
    simpa [prefixWord, tailWord_454733, baseEnd_454733] using wordTrace_append hprefix tailTrace_454733
  have hstable : (prefixWord ++ tailWord_454733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454733).length < 2 ^ (prefixWord ++ tailWord_454733).sum := by decide
  have hdescent : baseEnd_454733 < baseStart_454733 := by decide
  rcases family_descends (prefixWord ++ tailWord_454733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454739 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 7]
def baseStart_454739 : Nat := 118140960795 + 454739 * 2 ^ 59
def prefixEnd_454739 : Nat := 4983230072969 + 3 ^ 40 * 454739 * 2
def baseEnd_454739 : Nat := 233499679345001565271199

theorem tailTrace_454739 : CollatzResearch.WordTrace tailWord_454739 prefixEnd_454739 233499679345001565271199 := by
  unfold tailWord_454739
  simp only [CollatzResearch.WordTrace]
  refine ⟨16585693899565741083223271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11057129266377160722148847 16585693899565741083223271)
  ·
    refine ⟨24878540849348611624834907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16585693899565741083223271 24878540849348611624834907)
    ·
      refine ⟨37317811274022917437252361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24878540849348611624834907 37317811274022917437252361)
      ·
        refine ⟨27988358455517188077939271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37317811274022917437252361 27988358455517188077939271)
        ·
          refine ⟨41982537683275782116908907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27988358455517188077939271 41982537683275782116908907)
          ·
            refine ⟨62973806524913673175363361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41982537683275782116908907 62973806524913673175363361)
            ·
              refine ⟨47230354893685254881522521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62973806524913673175363361 47230354893685254881522521)
              ·
                refine ⟨35422766170263941161141891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47230354893685254881522521 35422766170263941161141891)
                ·
                  refine ⟨53134149255395911741712837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35422766170263941161141891 53134149255395911741712837)
                  ·
                    refine ⟨9962652985386733451571157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53134149255395911741712837 9962652985386733451571157)
                    ·
                      refine ⟨233499679345001565271199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 9962652985386733451571157 233499679345001565271199)
                      ·
                        rfl

theorem cell23_454739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 7].length) (baseStart_454739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454739 prefixEnd_454739 := by exact prefixLift 454739
  have htrace : WordTrace (prefixWord ++ tailWord_454739) baseStart_454739 baseEnd_454739 := by
    simpa [prefixWord, tailWord_454739, baseEnd_454739] using wordTrace_append hprefix tailTrace_454739
  have hstable : (prefixWord ++ tailWord_454739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454739).length < 2 ^ (prefixWord ++ tailWord_454739).sum := by decide
  have hdescent : baseEnd_454739 < baseStart_454739 := by decide
  rcases family_descends (prefixWord ++ tailWord_454739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454743 : List Nat := [1, 1, 3, 2, 2, 1, 2, 5, 1, 2, 3]
def baseStart_454743 : Nat := 118140960795 + 454743 * 2 ^ 59
def prefixEnd_454743 : Nat := 4983230072969 + 3 ^ 40 * 454743 * 2
def baseEnd_454743 : Nat := 233501733267619549621181

theorem tailTrace_454743 : CollatzResearch.WordTrace tailWord_454743 prefixEnd_454743 233501733267619549621181 := by
  unfold tailWord_454743
  simp only [CollatzResearch.WordTrace]
  refine ⟨16585839791551249766368883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11057226527700833177579255 16585839791551249766368883)
  ·
    refine ⟨24878759687326874649553325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16585839791551249766368883 24878759687326874649553325)
    ·
      refine ⟨9329534882747577993582497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24878759687326874649553325 9329534882747577993582497)
      ·
        refine ⟨6997151162060683495186873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9329534882747577993582497 6997151162060683495186873)
        ·
          refine ⟨5247863371545512621390155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6997151162060683495186873 5247863371545512621390155)
          ·
            refine ⟨7871795057318268932085233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5247863371545512621390155 7871795057318268932085233)
            ·
              refine ⟨5903846292988701699063925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7871795057318268932085233 5903846292988701699063925)
              ·
                refine ⟨553485589967690784287243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5903846292988701699063925 553485589967690784287243)
                ·
                  refine ⟨830228384951536176430865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 553485589967690784287243 830228384951536176430865)
                  ·
                    refine ⟨622671288713652132323149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 830228384951536176430865 622671288713652132323149)
                    ·
                      refine ⟨233501733267619549621181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 622671288713652132323149 233501733267619549621181)
                      ·
                        rfl

theorem cell23_454743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 5, 1, 2, 3].length) (baseStart_454743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454743 prefixEnd_454743 := by exact prefixLift 454743
  have htrace : WordTrace (prefixWord ++ tailWord_454743) baseStart_454743 baseEnd_454743 := by
    simpa [prefixWord, tailWord_454743, baseEnd_454743] using wordTrace_append hprefix tailTrace_454743
  have hstable : (prefixWord ++ tailWord_454743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454743).length < 2 ^ (prefixWord ++ tailWord_454743).sum := by decide
  have hdescent : baseEnd_454743 < baseStart_454743 := by decide
  rcases family_descends (prefixWord ++ tailWord_454743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454800 : List Nat := [2, 1, 1, 1, 1, 1, 7, 3, 1, 3, 2]
def baseStart_454800 : Nat := 118140960795 + 454800 * 2 ^ 59
def prefixEnd_454800 : Nat := 4983230072969 + 3 ^ 40 * 454800 * 2
def baseEnd_454800 : Nat := 233531001664925826608419

theorem tailTrace_454800 : CollatzResearch.WordTrace tailWord_454800 prefixEnd_454800 233531001664925826608419 := by
  unfold tailWord_454800
  simp only [CollatzResearch.WordTrace]
  refine ⟨8293959376172374250596927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11058612501563165667462569 8293959376172374250596927)
  ·
    refine ⟨12440939064258561375895391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8293959376172374250596927 12440939064258561375895391)
    ·
      refine ⟨18661408596387842063843087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12440939064258561375895391 18661408596387842063843087)
      ·
        refine ⟨27992112894581763095764631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18661408596387842063843087 27992112894581763095764631)
        ·
          refine ⟨41988169341872644643646947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27992112894581763095764631 41988169341872644643646947)
          ·
            refine ⟨62982254012808966965470421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41988169341872644643646947 62982254012808966965470421)
            ·
              refine ⟨1476146578425210163253213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 62982254012808966965470421 1476146578425210163253213)
              ·
                refine ⟨553554966909453811219955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1476146578425210163253213 553554966909453811219955)
                ·
                  refine ⟨830332450364180716829933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 553554966909453811219955 830332450364180716829933)
                  ·
                    refine ⟨311374668886567768811225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 830332450364180716829933 311374668886567768811225)
                    ·
                      refine ⟨233531001664925826608419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 311374668886567768811225 233531001664925826608419)
                      ·
                        rfl

theorem cell23_454800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 3, 1, 3, 2].length) (baseStart_454800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454800 prefixEnd_454800 := by exact prefixLift 454800
  have htrace : WordTrace (prefixWord ++ tailWord_454800) baseStart_454800 baseEnd_454800 := by
    simpa [prefixWord, tailWord_454800, baseEnd_454800] using wordTrace_append hprefix tailTrace_454800
  have hstable : (prefixWord ++ tailWord_454800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454800).length < 2 ^ (prefixWord ++ tailWord_454800).sum := by decide
  have hdescent : baseEnd_454800 < baseStart_454800 := by decide
  rcases family_descends (prefixWord ++ tailWord_454800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454896 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 2, 8]
def baseStart_454896 : Nat := 118140960795 + 454896 * 2 ^ 59
def prefixEnd_454896 : Nat := 4983230072969 + 3 ^ 40 * 454896 * 2
def baseEnd_454896 : Nat := 77860098602585817002659

theorem tailTrace_454896 : CollatzResearch.WordTrace tailWord_454896 prefixEnd_454896 77860098602585817002659 := by
  unfold tailWord_454896
  simp only [CollatzResearch.WordTrace]
  refine ⟨8295710079998478448344271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11060946773331304597792361 8295710079998478448344271)
  ·
    refine ⟨12443565119997717672516407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8295710079998478448344271 12443565119997717672516407)
    ·
      refine ⟨18665347679996576508774611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12443565119997717672516407 18665347679996576508774611)
      ·
        refine ⟨27998021519994864763161917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18665347679996576508774611 27998021519994864763161917)
        ·
          refine ⟨10499258069998074286185719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27998021519994864763161917 10499258069998074286185719)
          ·
            refine ⟨15748887104997111429278579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10499258069998074286185719 15748887104997111429278579)
            ·
              refine ⟨23623330657495667143917869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15748887104997111429278579 23623330657495667143917869)
              ·
                refine ⟨8858748996560875178969201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23623330657495667143917869 8858748996560875178969201)
                ·
                  refine ⟨6644061747420656384226901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8858748996560875178969201 6644061747420656384226901)
                  ·
                    refine ⟨77860098602585817002659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 6644061747420656384226901 77860098602585817002659)
                    ·
                      rfl

theorem cell23_454896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 2, 8].length) (baseStart_454896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454896 prefixEnd_454896 := by exact prefixLift 454896
  have htrace : WordTrace (prefixWord ++ tailWord_454896) baseStart_454896 baseEnd_454896 := by
    simpa [prefixWord, tailWord_454896, baseEnd_454896] using wordTrace_append hprefix tailTrace_454896
  have hstable : (prefixWord ++ tailWord_454896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454896).length < 2 ^ (prefixWord ++ tailWord_454896).sum := by decide
  have hdescent : baseEnd_454896 < baseStart_454896 := by decide
  rcases family_descends (prefixWord ++ tailWord_454896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454920 : List Nat := [2, 1, 3, 2, 3, 1, 2, 2, 2, 1, 4]
def baseStart_454920 : Nat := 118140960795 + 454920 * 2 ^ 59
def prefixEnd_454920 : Nat := 4983230072969 + 3 ^ 40 * 454920 * 2
def baseEnd_454920 : Nat := 233592619343465357107867

theorem tailTrace_454920 : CollatzResearch.WordTrace tailWord_454920 prefixEnd_454920 233592619343465357107867 := by
  unfold tailWord_454920
  simp only [CollatzResearch.WordTrace]
  refine ⟨8296147755955004497781107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11061530341273339330374809 8296147755955004497781107)
  ·
    refine ⟨12444221633932506746671661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8296147755955004497781107 12444221633932506746671661)
    ·
      refine ⟨4666583112724690030001873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12444221633932506746671661 4666583112724690030001873)
      ·
        refine ⟨3499937334543517522501405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4666583112724690030001873 3499937334543517522501405)
        ·
          refine ⟨1312476500453819070938027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3499937334543517522501405 1312476500453819070938027)
          ·
            refine ⟨1968714750680728606407041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1312476500453819070938027 1968714750680728606407041)
            ·
              refine ⟨1476536063010546454805281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1968714750680728606407041 1476536063010546454805281)
              ·
                refine ⟨1107402047257909841103961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1476536063010546454805281 1107402047257909841103961)
                ·
                  refine ⟨830551535443432380827971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1107402047257909841103961 830551535443432380827971)
                  ·
                    refine ⟨1245827303165148571241957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 830551535443432380827971 1245827303165148571241957)
                    ·
                      refine ⟨233592619343465357107867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1245827303165148571241957 233592619343465357107867)
                      ·
                        rfl

theorem cell23_454920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_454920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454920 prefixEnd_454920 := by exact prefixLift 454920
  have htrace : WordTrace (prefixWord ++ tailWord_454920) baseStart_454920 baseEnd_454920 := by
    simpa [prefixWord, tailWord_454920, baseEnd_454920] using wordTrace_append hprefix tailTrace_454920
  have hstable : (prefixWord ++ tailWord_454920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454920).length < 2 ^ (prefixWord ++ tailWord_454920).sum := by decide
  have hdescent : baseEnd_454920 < baseStart_454920 := by decide
  rcases family_descends (prefixWord ++ tailWord_454920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454951 : List Nat := [1, 1, 8, 1, 1, 2, 1, 1, 2, 5]
def baseStart_454951 : Nat := 118140960795 + 454951 * 2 ^ 59
def prefixEnd_454951 : Nat := 4983230072969 + 3 ^ 40 * 454951 * 2
def baseEnd_454951 : Nat := 77869512414584911940075

theorem tailTrace_454951 : CollatzResearch.WordTrace tailWord_454951 prefixEnd_454951 77869512414584911940075 := by
  unfold tailWord_454951
  simp only [CollatzResearch.WordTrace]
  refine ⟨16593426174797701289940707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11062284116531800859960471 16593426174797701289940707)
  ·
    refine ⟨24890139262196551934911061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16593426174797701289940707 24890139262196551934911061)
    ·
      refine ⟨291681319478865842987239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 24890139262196551934911061 291681319478865842987239)
      ·
        refine ⟨437521979218298764480859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291681319478865842987239 437521979218298764480859)
        ·
          refine ⟨656282968827448146721289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437521979218298764480859 656282968827448146721289)
          ·
            refine ⟨492212226620586110040967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 656282968827448146721289 492212226620586110040967)
            ·
              refine ⟨738318339930879165061451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 492212226620586110040967 738318339930879165061451)
              ·
                refine ⟨1107477509896318747592177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 738318339930879165061451 1107477509896318747592177)
                ·
                  refine ⟨830608132422239060694133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1107477509896318747592177 830608132422239060694133)
                  ·
                    refine ⟨77869512414584911940075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 830608132422239060694133 77869512414584911940075)
                    ·
                      rfl

theorem cell23_454951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_454951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454951 prefixEnd_454951 := by exact prefixLift 454951
  have htrace : WordTrace (prefixWord ++ tailWord_454951) baseStart_454951 baseEnd_454951 := by
    simpa [prefixWord, tailWord_454951, baseEnd_454951] using wordTrace_append hprefix tailTrace_454951
  have hstable : (prefixWord ++ tailWord_454951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454951).length < 2 ^ (prefixWord ++ tailWord_454951).sum := by decide
  have hdescent : baseEnd_454951 < baseStart_454951 := by decide
  rcases family_descends (prefixWord ++ tailWord_454951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454954 : List Nat := [3, 1, 4, 2, 2, 2, 1, 1, 2, 1, 4]
def baseStart_454954 : Nat := 118140960795 + 454954 * 2 ^ 59
def prefixEnd_454954 : Nat := 4983230072969 + 3 ^ 40 * 454954 * 2
def baseEnd_454954 : Nat := 233610077685718224082711

theorem tailTrace_454954 : CollatzResearch.WordTrace tailWord_454954 prefixEnd_454954 233610077685718224082711 := by
  unfold tailWord_454954
  simp only [CollatzResearch.WordTrace]
  refine ⟨4148383898446708200574979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11062357062524555201533277 4148383898446708200574979)
  ·
    refine ⟨6222575847670062300862469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4148383898446708200574979 6222575847670062300862469)
    ·
      refine ⟨1166732971438136681411713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6222575847670062300862469 1166732971438136681411713)
      ·
        refine ⟨875049728578602511058785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1166732971438136681411713 875049728578602511058785)
        ·
          refine ⟨656287296433951883294089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 875049728578602511058785 656287296433951883294089)
          ·
            refine ⟨492215472325463912470567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 656287296433951883294089 492215472325463912470567)
            ·
              refine ⟨738323208488195868705851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 492215472325463912470567 738323208488195868705851)
              ·
                refine ⟨1107484812732293803058777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 738323208488195868705851 1107484812732293803058777)
                ·
                  refine ⟨830613609549220352294083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1107484812732293803058777 830613609549220352294083)
                  ·
                    refine ⟨1245920414323830528441125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 830613609549220352294083 1245920414323830528441125)
                    ·
                      refine ⟨233610077685718224082711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1245920414323830528441125 233610077685718224082711)
                      ·
                        rfl

theorem cell23_454954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_454954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454954 prefixEnd_454954 := by exact prefixLift 454954
  have htrace : WordTrace (prefixWord ++ tailWord_454954) baseStart_454954 baseEnd_454954 := by
    simpa [prefixWord, tailWord_454954, baseEnd_454954] using wordTrace_append hprefix tailTrace_454954
  have hstable : (prefixWord ++ tailWord_454954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454954).length < 2 ^ (prefixWord ++ tailWord_454954).sum := by decide
  have hdescent : baseEnd_454954 < baseStart_454954 := by decide
  rcases family_descends (prefixWord ++ tailWord_454954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454964 : List Nat := [2, 5, 1, 1, 1, 2, 1, 5, 1, 4]
def baseStart_454964 : Nat := 118140960795 + 454964 * 2 ^ 59
def prefixEnd_454964 : Nat := 4983230072969 + 3 ^ 40 * 454964 * 2
def baseEnd_454964 : Nat := 77871737497421061652555

theorem tailTrace_454964 : CollatzResearch.WordTrace tailWord_454964 prefixEnd_454964 77871737497421061652555 := by
  unfold tailWord_454964
  simp only [CollatzResearch.WordTrace]
  refine ⟨8296950161875302255081973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11062600215833736340109297 8296950161875302255081973)
  ·
    refine ⟨777839077675809586413935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8296950161875302255081973 777839077675809586413935)
    ·
      refine ⟨1166758616513714379620903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 777839077675809586413935 1166758616513714379620903)
      ·
        refine ⟨1750137924770571569431355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1166758616513714379620903 1750137924770571569431355)
        ·
          refine ⟨2625206887155857354147033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1750137924770571569431355 2625206887155857354147033)
          ·
            refine ⟨1968905165366893015610275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2625206887155857354147033 1968905165366893015610275)
            ·
              refine ⟨2953357748050339523415413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1968905165366893015610275 2953357748050339523415413)
              ·
                refine ⟨276877288879719330320195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2953357748050339523415413 276877288879719330320195)
                ·
                  refine ⟨415315933319578995480293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 276877288879719330320195 415315933319578995480293)
                  ·
                    refine ⟨77871737497421061652555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 415315933319578995480293 77871737497421061652555)
                    ·
                      rfl

theorem cell23_454964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_454964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_454964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_454964 prefixEnd_454964 := by exact prefixLift 454964
  have htrace : WordTrace (prefixWord ++ tailWord_454964) baseStart_454964 baseEnd_454964 := by
    simpa [prefixWord, tailWord_454964, baseEnd_454964] using wordTrace_append hprefix tailTrace_454964
  have hstable : (prefixWord ++ tailWord_454964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454964).length < 2 ^ (prefixWord ++ tailWord_454964).sum := by decide
  have hdescent : baseEnd_454964 < baseStart_454964 := by decide
  rcases family_descends (prefixWord ++ tailWord_454964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455054 : List Nat := [4, 1, 1, 4, 1, 2, 1, 3, 2, 4]
def baseStart_455054 : Nat := 118140960795 + 455054 * 2 ^ 59
def prefixEnd_455054 : Nat := 4983230072969 + 3 ^ 40 * 455054 * 2
def baseEnd_455054 : Nat := 77887141917055944277417

theorem tailTrace_455054 : CollatzResearch.WordTrace tailWord_455054 prefixEnd_455054 77887141917055944277417 := by
  unfold tailWord_455054
  simp only [CollatzResearch.WordTrace]
  refine ⟨2074647861678068735117527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11064788595616366587293477 2074647861678068735117527)
  ·
    refine ⟨3111971792517103102676291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2074647861678068735117527 3111971792517103102676291)
    ·
      refine ⟨4667957688775654654014437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3111971792517103102676291 4667957688775654654014437)
      ·
        refine ⟨875242066645435247627707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4667957688775654654014437 875242066645435247627707)
        ·
          refine ⟨1312863099968152871441561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 875242066645435247627707 1312863099968152871441561)
          ·
            refine ⟨984647324976114653581171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1312863099968152871441561 984647324976114653581171)
            ·
              refine ⟨1476970987464171980371757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 984647324976114653581171 1476970987464171980371757)
              ·
                refine ⟨553864120299064492639409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1476970987464171980371757 553864120299064492639409)
                ·
                  refine ⟨415398090224298369479557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 553864120299064492639409 415398090224298369479557)
                  ·
                    refine ⟨77887141917055944277417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 415398090224298369479557 77887141917055944277417)
                    ·
                      rfl

theorem cell23_455054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 3, 2, 4].length) (baseStart_455054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_455054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_455054 prefixEnd_455054 := by exact prefixLift 455054
  have htrace : WordTrace (prefixWord ++ tailWord_455054) baseStart_455054 baseEnd_455054 := by
    simpa [prefixWord, tailWord_455054, baseEnd_455054] using wordTrace_append hprefix tailTrace_455054
  have hstable : (prefixWord ++ tailWord_455054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455054).length < 2 ^ (prefixWord ++ tailWord_455054).sum := by decide
  have hdescent : baseEnd_455054 < baseStart_455054 := by decide
  rcases family_descends (prefixWord ++ tailWord_455054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455064 : List Nat := [2, 1, 2, 5, 1, 1, 3, 2, 1, 2, 3]
def baseStart_455064 : Nat := 118140960795 + 455064 * 2 ^ 59
def prefixEnd_455064 : Nat := 4983230072969 + 3 ^ 40 * 455064 * 2
def baseEnd_455064 : Nat := 233666560557712793707205

theorem tailTrace_455064 : CollatzResearch.WordTrace tailWord_455064 prefixEnd_455064 233666560557712793707205 := by
  unfold tailWord_455064
  simp only [CollatzResearch.WordTrace]
  refine ⟨8298773811694160794402123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11065031748925547725869497 8298773811694160794402123)
  ·
    refine ⟨12448160717541241191603185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8298773811694160794402123 12448160717541241191603185)
    ·
      refine ⟨9336120538155930893702389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12448160717541241191603185 9336120538155930893702389)
      ·
        refine ⟨875261300452118521284599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9336120538155930893702389 875261300452118521284599)
        ·
          refine ⟨1312891950678177781926899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 875261300452118521284599 1312891950678177781926899)
          ·
            refine ⟨1969337926017266672890349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1312891950678177781926899 1969337926017266672890349)
            ·
              refine ⟨738501722256475002333881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1969337926017266672890349 738501722256475002333881)
              ·
                refine ⟨553876291692356251750411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 738501722256475002333881 553876291692356251750411)
                ·
                  refine ⟨830814437538534377625617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 553876291692356251750411 830814437538534377625617)
                  ·
                    refine ⟨623110828153900783219213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 830814437538534377625617 623110828153900783219213)
                    ·
                      refine ⟨233666560557712793707205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 623110828153900783219213 233666560557712793707205)
                      ·
                        rfl

theorem cell23_455064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_455064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_455064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_455064 prefixEnd_455064 := by exact prefixLift 455064
  have htrace : WordTrace (prefixWord ++ tailWord_455064) baseStart_455064 baseEnd_455064 := by
    simpa [prefixWord, tailWord_455064, baseEnd_455064] using wordTrace_append hprefix tailTrace_455064
  have hstable : (prefixWord ++ tailWord_455064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455064).length < 2 ^ (prefixWord ++ tailWord_455064).sum := by decide
  have hdescent : baseEnd_455064 < baseStart_455064 := by decide
  rcases family_descends (prefixWord ++ tailWord_455064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455130 : List Nat := [3, 1, 1, 2, 3, 1, 1, 2, 1, 4, 4]
def baseStart_455130 : Nat := 118140960795 + 455130 * 2 ^ 59
def prefixEnd_455130 : Nat := 4983230072969 + 3 ^ 40 * 455130 * 2
def baseEnd_455130 : Nat := 233700450280909535481901

theorem tailTrace_455130 : CollatzResearch.WordTrace tailWord_455130 prefixEnd_455130 233700450280909535481901 := by
  unfold tailWord_455130
  simp only [CollatzResearch.WordTrace]
  refine ⟨4149988710287303715176711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11066636560766143240471229 4149988710287303715176711)
  ·
    refine ⟨6224983065430955572765067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4149988710287303715176711 6224983065430955572765067)
    ·
      refine ⟨9337474598146433359147601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6224983065430955572765067 9337474598146433359147601)
      ·
        refine ⟨7003105948609825019360701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9337474598146433359147601 7003105948609825019360701)
        ·
          refine ⟨2626164730728684382260263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7003105948609825019360701 2626164730728684382260263)
          ·
            refine ⟨3939247096093026573390395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2626164730728684382260263 3939247096093026573390395)
            ·
              refine ⟨5908870644139539860085593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3939247096093026573390395 5908870644139539860085593)
              ·
                refine ⟨4431652983104654895064195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5908870644139539860085593 4431652983104654895064195)
                ·
                  refine ⟨6647479474656982342596293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4431652983104654895064195 6647479474656982342596293)
                  ·
                    refine ⟨1246402401498184189236805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6647479474656982342596293 1246402401498184189236805)
                    ·
                      refine ⟨233700450280909535481901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1246402401498184189236805 233700450280909535481901)
                      ·
                        rfl

theorem cell23_455130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_455130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_455130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_455130 prefixEnd_455130 := by exact prefixLift 455130
  have htrace : WordTrace (prefixWord ++ tailWord_455130) baseStart_455130 baseEnd_455130 := by
    simpa [prefixWord, tailWord_455130, baseEnd_455130] using wordTrace_append hprefix tailTrace_455130
  have hstable : (prefixWord ++ tailWord_455130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455130).length < 2 ^ (prefixWord ++ tailWord_455130).sum := by decide
  have hdescent : baseEnd_455130 < baseStart_455130 := by decide
  rcases family_descends (prefixWord ++ tailWord_455130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455214 : List Nat := [4, 1, 3, 1, 3, 1, 1, 1, 1, 2, 5]
def baseStart_455214 : Nat := 118140960795 + 455214 * 2 ^ 59
def prefixEnd_455214 : Nat := 4983230072969 + 3 ^ 40 * 455214 * 2
def baseEnd_455214 : Nat := 233743582655887206831515

theorem tailTrace_455214 : CollatzResearch.WordTrace tailWord_455214 prefixEnd_455214 233743582655887206831515 := by
  unfold tailWord_455214
  simp only [CollatzResearch.WordTrace]
  refine ⟨2075377321605612150845587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11068679048563264804509797 2075377321605612150845587)
  ·
    refine ⟨3113065982408418226268381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2075377321605612150845587 3113065982408418226268381)
    ·
      refine ⟨1167399743403156834850643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3113065982408418226268381 1167399743403156834850643)
      ·
        refine ⟨1751099615104735252275965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1167399743403156834850643 1751099615104735252275965)
        ·
          refine ⟨656662355664275719603487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1751099615104735252275965 656662355664275719603487)
          ·
            refine ⟨984993533496413579405231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 656662355664275719603487 984993533496413579405231)
            ·
              refine ⟨1477490300244620369107847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 984993533496413579405231 1477490300244620369107847)
              ·
                refine ⟨2216235450366930553661771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1477490300244620369107847 2216235450366930553661771)
                ·
                  refine ⟨3324353175550395830492657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2216235450366930553661771 3324353175550395830492657)
                  ·
                    refine ⟨2493264881662796872869493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3324353175550395830492657 2493264881662796872869493)
                    ·
                      refine ⟨233743582655887206831515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2493264881662796872869493 233743582655887206831515)
                      ·
                        rfl

theorem cell23_455214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_455214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_455214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_455214 prefixEnd_455214 := by exact prefixLift 455214
  have htrace : WordTrace (prefixWord ++ tailWord_455214) baseStart_455214 baseEnd_455214 := by
    simpa [prefixWord, tailWord_455214, baseEnd_455214] using wordTrace_append hprefix tailTrace_455214
  have hstable : (prefixWord ++ tailWord_455214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455214).length < 2 ^ (prefixWord ++ tailWord_455214).sum := by decide
  have hdescent : baseEnd_455214 < baseStart_455214 := by decide
  rcases family_descends (prefixWord ++ tailWord_455214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455244 : List Nat := [2, 2, 1, 3, 1, 2, 4, 1, 2, 2, 3]
def baseStart_455244 : Nat := 118140960795 + 455244 * 2 ^ 59
def prefixEnd_455244 : Nat := 4983230072969 + 3 ^ 40 * 455244 * 2
def baseEnd_455244 : Nat := 233758987075522089456377

theorem tailTrace_455244 : CollatzResearch.WordTrace tailWord_455244 prefixEnd_455244 233758987075522089456377 := by
  unfold tailWord_455244
  simp only [CollatzResearch.WordTrace]
  refine ⟨8302056381368106165178393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11069408508490808220237857 8302056381368106165178393)
  ·
    refine ⟨6226542286026079623883795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8302056381368106165178393 6226542286026079623883795)
    ·
      refine ⟨9339813429039119435825693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6226542286026079623883795 9339813429039119435825693)
      ·
        refine ⟨3502430035889669788434635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9339813429039119435825693 3502430035889669788434635)
        ·
          refine ⟨5253645053834504682651953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3502430035889669788434635 5253645053834504682651953)
          ·
            refine ⟨3940233790375878511988965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5253645053834504682651953 3940233790375878511988965)
            ·
              refine ⟨738793835695477220997931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3940233790375878511988965 738793835695477220997931)
              ·
                refine ⟨1108190753543215831496897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 738793835695477220997931 1108190753543215831496897)
                ·
                  refine ⟨831143065157411873622673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1108190753543215831496897 831143065157411873622673)
                  ·
                    refine ⟨623357298868058905217005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 831143065157411873622673 623357298868058905217005)
                    ·
                      refine ⟨233758987075522089456377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 623357298868058905217005 233758987075522089456377)
                      ·
                        rfl

theorem cell23_455244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_455244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_455244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_455244 prefixEnd_455244 := by exact prefixLift 455244
  have htrace : WordTrace (prefixWord ++ tailWord_455244) baseStart_455244 baseEnd_455244 := by
    simpa [prefixWord, tailWord_455244, baseEnd_455244] using wordTrace_append hprefix tailTrace_455244
  have hstable : (prefixWord ++ tailWord_455244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455244).length < 2 ^ (prefixWord ++ tailWord_455244).sum := by decide
  have hdescent : baseEnd_455244 < baseStart_455244 := by decide
  rcases family_descends (prefixWord ++ tailWord_455244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455301 : List Nat := [1, 3, 1, 1, 4, 2, 3, 1, 2, 3, 2]
def baseStart_455301 : Nat := 118140960795 + 455301 * 2 ^ 59
def prefixEnd_455301 : Nat := 4983230072969 + 3 ^ 40 * 455301 * 2
def baseEnd_455301 : Nat := 233788255472828366443615

theorem tailTrace_455301 : CollatzResearch.WordTrace tailWord_455301 prefixEnd_455301 233788255472828366443615 := by
  unfold tailWord_455301
  simp only [CollatzResearch.WordTrace]
  refine ⟨16606191723529711065181757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11070794482353140710121171 16606191723529711065181757)
  ·
    refine ⟨6227321896323641649443159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16606191723529711065181757 6227321896323641649443159)
    ·
      refine ⟨9340982844485462474164739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6227321896323641649443159 9340982844485462474164739)
      ·
        refine ⟨14011474266728193711247109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9340982844485462474164739 14011474266728193711247109)
        ·
          refine ⟨2627151425011536320858833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14011474266728193711247109 2627151425011536320858833)
          ·
            refine ⟨1970363568758652240644125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2627151425011536320858833 1970363568758652240644125)
            ·
              refine ⟨738886338284494590241547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1970363568758652240644125 738886338284494590241547)
              ·
                refine ⟨1108329507426741885362321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 738886338284494590241547 1108329507426741885362321)
                ·
                  refine ⟨831247130570056414021741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1108329507426741885362321 831247130570056414021741)
                  ·
                    refine ⟨311717673963771155258153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 831247130570056414021741 311717673963771155258153)
                    ·
                      refine ⟨233788255472828366443615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 311717673963771155258153 233788255472828366443615)
                      ·
                        rfl

theorem cell23_455301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 2, 3, 2].length) (baseStart_455301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_455301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_455301 prefixEnd_455301 := by exact prefixLift 455301
  have htrace : WordTrace (prefixWord ++ tailWord_455301) baseStart_455301 baseEnd_455301 := by
    simpa [prefixWord, tailWord_455301, baseEnd_455301] using wordTrace_append hprefix tailTrace_455301
  have hstable : (prefixWord ++ tailWord_455301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455301).length < 2 ^ (prefixWord ++ tailWord_455301).sum := by decide
  have hdescent : baseEnd_455301 < baseStart_455301 := by decide
  rcases family_descends (prefixWord ++ tailWord_455301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455341 : List Nat := [1, 5, 2, 1, 1, 4, 1, 1, 1, 6]
def baseStart_455341 : Nat := 118140960795 + 455341 * 2 ^ 59
def prefixEnd_455341 : Nat := 4983230072969 + 3 ^ 40 * 455341 * 2
def baseEnd_455341 : Nat := 77936264899669403314477

theorem tailTrace_455341 : CollatzResearch.WordTrace tailWord_455341 prefixEnd_455341 77936264899669403314477 := by
  unfold tailWord_455341
  simp only [CollatzResearch.WordTrace]
  refine ⟨16607650643384797896637877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11071767095589865264425251 16607650643384797896637877)
  ·
    refine ⟨1556967247817324802809801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16607650643384797896637877 1556967247817324802809801)
    ·
      refine ⟨1167725435862993602107351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1556967247817324802809801 1167725435862993602107351)
      ·
        refine ⟨1751588153794490403161027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1167725435862993602107351 1751588153794490403161027)
        ·
          refine ⟨2627382230691735604741541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1751588153794490403161027 2627382230691735604741541)
          ·
            refine ⟨492634168254700425889039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2627382230691735604741541 492634168254700425889039)
            ·
              refine ⟨738951252382050638833559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 492634168254700425889039 738951252382050638833559)
              ·
                refine ⟨1108426878573075958250339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 738951252382050638833559 1108426878573075958250339)
                ·
                  refine ⟨1662640317859613937375509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1108426878573075958250339 1662640317859613937375509)
                  ·
                    refine ⟨77936264899669403314477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1662640317859613937375509 77936264899669403314477)
                    ·
                      rfl

theorem cell23_455341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_455341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_455341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_455341 prefixEnd_455341 := by exact prefixLift 455341
  have htrace : WordTrace (prefixWord ++ tailWord_455341) baseStart_455341 baseEnd_455341 := by
    simpa [prefixWord, tailWord_455341, baseEnd_455341] using wordTrace_append hprefix tailTrace_455341
  have hstable : (prefixWord ++ tailWord_455341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455341).length < 2 ^ (prefixWord ++ tailWord_455341).sum := by decide
  have hdescent : baseEnd_455341 < baseStart_455341 := by decide
  rcases family_descends (prefixWord ++ tailWord_455341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455377 : List Nat := [1, 2, 2, 1, 2, 3, 1, 2, 2, 2, 5]
def baseStart_455377 : Nat := 118140960795 + 455377 * 2 ^ 59
def prefixEnd_455377 : Nat := 4983230072969 + 3 ^ 40 * 455377 * 2
def baseEnd_455377 : Nat := 233827280002570069093265

theorem tailTrace_455377 : CollatzResearch.WordTrace tailWord_455377 prefixEnd_455377 233827280002570069093265 := by
  unfold tailWord_455377
  simp only [CollatzResearch.WordTrace]
  refine ⟨16608963671254376044948385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11072642447502917363298923 16608963671254376044948385)
  ·
    refine ⟨12456722753440782033711289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16608963671254376044948385 12456722753440782033711289)
    ·
      refine ⟨9342542065080586525283467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12456722753440782033711289 9342542065080586525283467)
      ·
        refine ⟨14013813097620879787925201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9342542065080586525283467 14013813097620879787925201)
        ·
          refine ⟨10510359823215659840943901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14013813097620879787925201 10510359823215659840943901)
          ·
            refine ⟨3941384933705872440353963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10510359823215659840943901 3941384933705872440353963)
            ·
              refine ⟨5912077400558808660530945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3941384933705872440353963 5912077400558808660530945)
              ·
                refine ⟨4434058050419106495398209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5912077400558808660530945 4434058050419106495398209)
                ·
                  refine ⟨3325543537814329871548657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4434058050419106495398209 3325543537814329871548657)
                  ·
                    refine ⟨2494157653360747403661493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3325543537814329871548657 2494157653360747403661493)
                    ·
                      refine ⟨233827280002570069093265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2494157653360747403661493 233827280002570069093265)
                      ·
                        rfl

theorem cell23_455377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_455377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_455377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_455377 prefixEnd_455377 := by exact prefixLift 455377
  have htrace : WordTrace (prefixWord ++ tailWord_455377) baseStart_455377 baseEnd_455377 := by
    simpa [prefixWord, tailWord_455377, baseEnd_455377] using wordTrace_append hprefix tailTrace_455377
  have hstable : (prefixWord ++ tailWord_455377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455377).length < 2 ^ (prefixWord ++ tailWord_455377).sum := by decide
  have hdescent : baseEnd_455377 < baseStart_455377 := by decide
  rcases family_descends (prefixWord ++ tailWord_455377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455421 : List Nat := [1, 4, 1, 1, 1, 1, 5, 2, 1, 4, 2]
def baseStart_455421 : Nat := 118140960795 + 455421 * 2 ^ 59
def prefixEnd_455421 : Nat := 4983230072969 + 3 ^ 40 * 455421 * 2
def baseEnd_455421 : Nat := 233849873151367896943063

theorem tailTrace_455421 : CollatzResearch.WordTrace tailWord_455421 prefixEnd_455421 233849873151367896943063 := by
  unfold tailWord_455421
  simp only [CollatzResearch.WordTrace]
  refine ⟨16610568483094971559550117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11073712322063314373033411 16610568483094971559550117)
  ·
    refine ⟨3114481590580307167415647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16610568483094971559550117 3114481590580307167415647)
    ·
      refine ⟨4671722385870460751123471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3114481590580307167415647 4671722385870460751123471)
      ·
        refine ⟨7007583578805691126685207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4671722385870460751123471 7007583578805691126685207)
        ·
          refine ⟨10511375368208536690027811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7007583578805691126685207 10511375368208536690027811)
          ·
            refine ⟨15767063052312805035041717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10511375368208536690027811 15767063052312805035041717)
            ·
              refine ⟨1478162161154325472035161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15767063052312805035041717 1478162161154325472035161)
              ·
                refine ⟨1108621620865744104026371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1478162161154325472035161 1108621620865744104026371)
                ·
                  refine ⟨1662932431298616156039557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1108621620865744104026371 1662932431298616156039557)
                  ·
                    refine ⟨311799830868490529257417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1662932431298616156039557 311799830868490529257417)
                    ·
                      refine ⟨233849873151367896943063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 311799830868490529257417 233849873151367896943063)
                      ·
                        rfl

theorem cell23_455421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 4, 2].length) (baseStart_455421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_455421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_455421 prefixEnd_455421 := by exact prefixLift 455421
  have htrace : WordTrace (prefixWord ++ tailWord_455421) baseStart_455421 baseEnd_455421 := by
    simpa [prefixWord, tailWord_455421, baseEnd_455421] using wordTrace_append hprefix tailTrace_455421
  have hstable : (prefixWord ++ tailWord_455421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455421).length < 2 ^ (prefixWord ++ tailWord_455421).sum := by decide
  have hdescent : baseEnd_455421 < baseStart_455421 := by decide
  rcases family_descends (prefixWord ++ tailWord_455421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455434 : List Nat := [3, 1, 2, 2, 1, 2, 2, 2, 2, 2, 4]
def baseStart_455434 : Nat := 118140960795 + 455434 * 2 ^ 59
def prefixEnd_455434 : Nat := 4983230072969 + 3 ^ 40 * 455434 * 2
def baseEnd_455434 : Nat := 233856548399876346080503

theorem tailTrace_455434 : CollatzResearch.WordTrace tailWord_455434 prefixEnd_455434 233856548399876346080503 := by
  unfold tailWord_455434
  simp only [CollatzResearch.WordTrace]
  refine ⟨4152760658011968694943339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11074028421365249853182237 4152760658011968694943339)
  ·
    refine ⟨6229140987017953042415009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4152760658011968694943339 6229140987017953042415009)
    ·
      refine ⟨4671855740263464781811257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6229140987017953042415009 4671855740263464781811257)
      ·
        refine ⟨3503891805197598586358443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4671855740263464781811257 3503891805197598586358443)
        ·
          refine ⟨5255837707796397879537665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3503891805197598586358443 5255837707796397879537665)
          ·
            refine ⟨3941878280847298409653249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5255837707796397879537665 3941878280847298409653249)
            ·
              refine ⟨2956408710635473807239937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3941878280847298409653249 2956408710635473807239937)
              ·
                refine ⟨2217306532976605355429953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2956408710635473807239937 2217306532976605355429953)
                ·
                  refine ⟨1662979899732454016572465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2217306532976605355429953 1662979899732454016572465)
                  ·
                    refine ⟨1247234924799340512429349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1662979899732454016572465 1247234924799340512429349)
                    ·
                      refine ⟨233856548399876346080503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1247234924799340512429349 233856548399876346080503)
                      ·
                        rfl

theorem cell23_455434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_455434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_455434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_455434 prefixEnd_455434 := by exact prefixLift 455434
  have htrace : WordTrace (prefixWord ++ tailWord_455434) baseStart_455434 baseEnd_455434 := by
    simpa [prefixWord, tailWord_455434, baseEnd_455434] using wordTrace_append hprefix tailTrace_455434
  have hstable : (prefixWord ++ tailWord_455434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455434).length < 2 ^ (prefixWord ++ tailWord_455434).sum := by decide
  have hdescent : baseEnd_455434 < baseStart_455434 := by decide
  rcases family_descends (prefixWord ++ tailWord_455434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455467 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 7]
def baseStart_455467 : Nat := 118140960795 + 455467 * 2 ^ 59
def prefixEnd_455467 : Nat := 4983230072969 + 3 ^ 40 * 455467 * 2
def baseEnd_455467 : Nat := 233873493261474716967851

theorem tailTrace_455467 : CollatzResearch.WordTrace tailWord_455467 prefixEnd_455467 233873493261474716967851 := by
  unfold tailWord_455467
  simp only [CollatzResearch.WordTrace]
  refine ⟨16612246240928321415724655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11074830827285547610483103 16612246240928321415724655)
  ·
    refine ⟨24918369361392482123586983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16612246240928321415724655 24918369361392482123586983)
    ·
      refine ⟨37377554042088723185380475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24918369361392482123586983 37377554042088723185380475)
      ·
        refine ⟨56066331063133084778070713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37377554042088723185380475 56066331063133084778070713)
        ·
          refine ⟨42049748297349813583553035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56066331063133084778070713 42049748297349813583553035)
          ·
            refine ⟨63074622446024720375329553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42049748297349813583553035 63074622446024720375329553)
            ·
              refine ⟨47305966834518540281497165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63074622446024720375329553 47305966834518540281497165)
              ·
                refine ⟨17739737562944452605561437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47305966834518540281497165 17739737562944452605561437)
                ·
                  refine ⟨6652401586104169727085539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17739737562944452605561437 6652401586104169727085539)
                  ·
                    refine ⟨9978602379156254590628309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6652401586104169727085539 9978602379156254590628309)
                    ·
                      refine ⟨233873493261474716967851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 9978602379156254590628309 233873493261474716967851)
                      ·
                        rfl

theorem cell23_455467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 7].length) (baseStart_455467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_455467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_455467 prefixEnd_455467 := by exact prefixLift 455467
  have htrace : WordTrace (prefixWord ++ tailWord_455467) baseStart_455467 baseEnd_455467 := by
    simpa [prefixWord, tailWord_455467, baseEnd_455467] using wordTrace_append hprefix tailTrace_455467
  have hstable : (prefixWord ++ tailWord_455467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455467).length < 2 ^ (prefixWord ++ tailWord_455467).sum := by decide
  have hdescent : baseEnd_455467 < baseStart_455467 := by decide
  rcases family_descends (prefixWord ++ tailWord_455467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455474 : List Nat := [3, 2, 1, 1, 3, 1, 3, 1, 1, 7]
def baseStart_455474 : Nat := 118140960795 + 455474 * 2 ^ 59
def prefixEnd_455474 : Nat := 4983230072969 + 3 ^ 40 * 455474 * 2
def baseEnd_455474 : Nat := 77959029208685396526773

theorem tailTrace_455474 : CollatzResearch.WordTrace tailWord_455474 prefixEnd_455474 77959029208685396526773 := by
  unfold tailWord_455474
  simp only [CollatzResearch.WordTrace]
  refine ⟨4153125387975740402807369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11075001034601974407486317 4153125387975740402807369)
  ·
    refine ⟨3114844040981805302105527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4153125387975740402807369 3114844040981805302105527)
    ·
      refine ⟨4672266061472707953158291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3114844040981805302105527 4672266061472707953158291)
      ·
        refine ⟨7008399092209061929737437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4672266061472707953158291 7008399092209061929737437)
        ·
          refine ⟨2628149659578398223651539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7008399092209061929737437 2628149659578398223651539)
          ·
            refine ⟨3942224489367597335477309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2628149659578398223651539 3942224489367597335477309)
            ·
              refine ⟨1478334183512849000803991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3942224489367597335477309 1478334183512849000803991)
              ·
                refine ⟨2217501275269273501205987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1478334183512849000803991 2217501275269273501205987)
                ·
                  refine ⟨3326251912903910251808981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2217501275269273501205987 3326251912903910251808981)
                  ·
                    refine ⟨77959029208685396526773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3326251912903910251808981 77959029208685396526773)
                    ·
                      rfl

theorem cell23_455474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_455474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_455474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_455474 prefixEnd_455474 := by exact prefixLift 455474
  have htrace : WordTrace (prefixWord ++ tailWord_455474) baseStart_455474 baseEnd_455474 := by
    simpa [prefixWord, tailWord_455474, baseEnd_455474] using wordTrace_append hprefix tailTrace_455474
  have hstable : (prefixWord ++ tailWord_455474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455474).length < 2 ^ (prefixWord ++ tailWord_455474).sum := by decide
  have hdescent : baseEnd_455474 < baseStart_455474 := by decide
  rcases family_descends (prefixWord ++ tailWord_455474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455489 : List Nat := [1, 2, 5, 3, 1, 2, 1, 2, 2, 2, 2]
def baseStart_455489 : Nat := 118140960795 + 455489 * 2 ^ 59
def prefixEnd_455489 : Nat := 4983230072969 + 3 ^ 40 * 455489 * 2
def baseEnd_455489 : Nat := 233884789835873630892751

theorem tailTrace_455489 : CollatzResearch.WordTrace tailWord_455489 prefixEnd_455489 233884789835873630892751 := by
  unfold tailWord_455489
  simp only [CollatzResearch.WordTrace]
  refine ⟨16613048646848619173025521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11075365764565746115350347 16613048646848619173025521)
  ·
    refine ⟨12459786485136464379769141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16613048646848619173025521 12459786485136464379769141)
    ·
      refine ⟨1168104982981543535603357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12459786485136464379769141 1168104982981543535603357)
      ·
        refine ⟨438039368618078825851259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1168104982981543535603357 438039368618078825851259)
        ·
          refine ⟨657059052927118238776889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438039368618078825851259 657059052927118238776889)
          ·
            refine ⟨492794289695338679082667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 657059052927118238776889 492794289695338679082667)
            ·
              refine ⟨739191434543008018624001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 492794289695338679082667 739191434543008018624001)
              ·
                refine ⟨554393575907256013968001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 739191434543008018624001 554393575907256013968001)
                ·
                  refine ⟨415795181930442010476001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 554393575907256013968001 415795181930442010476001)
                  ·
                    refine ⟨311846386447831507857001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 415795181930442010476001 311846386447831507857001)
                    ·
                      refine ⟨233884789835873630892751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 311846386447831507857001 233884789835873630892751)
                      ·
                        rfl

theorem cell23_455489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_455489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_455489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_455489 prefixEnd_455489 := by exact prefixLift 455489
  have htrace : WordTrace (prefixWord ++ tailWord_455489) baseStart_455489 baseEnd_455489 := by
    simpa [prefixWord, tailWord_455489, baseEnd_455489] using wordTrace_append hprefix tailTrace_455489
  have hstable : (prefixWord ++ tailWord_455489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455489).length < 2 ^ (prefixWord ++ tailWord_455489).sum := by decide
  have hdescent : baseEnd_455489 < baseStart_455489 := by decide
  rcases family_descends (prefixWord ++ tailWord_455489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455555 : List Nat := [1, 1, 1, 3, 4, 1, 5, 2, 1, 4]
def baseStart_455555 : Nat := 118140960795 + 455555 * 2 ^ 59
def prefixEnd_455555 : Nat := 4983230072969 + 3 ^ 40 * 455555 * 2
def baseEnd_455555 : Nat := 77972893186356790889149

theorem tailTrace_455555 : CollatzResearch.WordTrace tailWord_455555 prefixEnd_455555 77972893186356790889149 := by
  unfold tailWord_455555
  simp only [CollatzResearch.WordTrace]
  refine ⟨16615455864609512444928119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11076970576406341629952079 16615455864609512444928119)
  ·
    refine ⟨24923183796914268667392179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16615455864609512444928119 24923183796914268667392179)
    ·
      refine ⟨37384775695371403001088269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24923183796914268667392179 37384775695371403001088269)
      ·
        refine ⟨14019290885764276125408101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37384775695371403001088269 14019290885764276125408101)
        ·
          refine ⟨2628617041080801773514019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14019290885764276125408101 2628617041080801773514019)
          ·
            refine ⟨3942925561621202660271029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2628617041080801773514019 3942925561621202660271029)
            ·
              refine ⟨369649271401987749400409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3942925561621202660271029 369649271401987749400409)
              ·
                refine ⟨277236953551490812050307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 369649271401987749400409 277236953551490812050307)
                ·
                  refine ⟨415855430327236218075461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 277236953551490812050307 415855430327236218075461)
                  ·
                    refine ⟨77972893186356790889149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 415855430327236218075461 77972893186356790889149)
                    ·
                      rfl

theorem cell23_455555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 2, 1, 4].length) (baseStart_455555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_455555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_455555 prefixEnd_455555 := by exact prefixLift 455555
  have htrace : WordTrace (prefixWord ++ tailWord_455555) baseStart_455555 baseEnd_455555 := by
    simpa [prefixWord, tailWord_455555, baseEnd_455555] using wordTrace_append hprefix tailTrace_455555
  have hstable : (prefixWord ++ tailWord_455555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455555).length < 2 ^ (prefixWord ++ tailWord_455555).sum := by decide
  have hdescent : baseEnd_455555 < baseStart_455555 := by decide
  rcases family_descends (prefixWord ++ tailWord_455555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455571 : List Nat := [1, 1, 1, 2, 1, 2, 1, 6, 1, 5, 2]
def baseStart_455571 : Nat := 118140960795 + 455571 * 2 ^ 59
def prefixEnd_455571 : Nat := 4983230072969 + 3 ^ 40 * 455571 * 2
def baseEnd_455571 : Nat := 233926895249542310067373

theorem tailTrace_455571 : CollatzResearch.WordTrace tailWord_455571 prefixEnd_455571 233926895249542310067373 := by
  unfold tailWord_455571
  simp only [CollatzResearch.WordTrace]
  refine ⟨16616039432551547177510567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11077359621701031451673711 16616039432551547177510567)
  ·
    refine ⟨24924059148827320766265851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16616039432551547177510567 24924059148827320766265851)
    ·
      refine ⟨37386088723240981149398777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24924059148827320766265851 37386088723240981149398777)
      ·
        refine ⟨28039566542430735862049083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37386088723240981149398777 28039566542430735862049083)
        ·
          refine ⟨42059349813646103793073625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28039566542430735862049083 42059349813646103793073625)
          ·
            refine ⟨31544512360234577844805219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42059349813646103793073625 31544512360234577844805219)
            ·
              refine ⟨47316768540351866767207829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31544512360234577844805219 47316768540351866767207829)
              ·
                refine ⟨2217973525328993754712867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47316768540351866767207829 2217973525328993754712867)
                ·
                  refine ⟨3326960287993490632069301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2217973525328993754712867 3326960287993490632069301)
                  ·
                    refine ⟨311902526999389746756497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3326960287993490632069301 311902526999389746756497)
                    ·
                      refine ⟨233926895249542310067373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 311902526999389746756497 233926895249542310067373)
                      ·
                        rfl

theorem cell23_455571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 5, 2].length) (baseStart_455571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_455571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_455571 prefixEnd_455571 := by exact prefixLift 455571
  have htrace : WordTrace (prefixWord ++ tailWord_455571) baseStart_455571 baseEnd_455571 := by
    simpa [prefixWord, tailWord_455571, baseEnd_455571] using wordTrace_append hprefix tailTrace_455571
  have hstable : (prefixWord ++ tailWord_455571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455571).length < 2 ^ (prefixWord ++ tailWord_455571).sum := by decide
  have hdescent : baseEnd_455571 < baseStart_455571 := by decide
  rcases family_descends (prefixWord ++ tailWord_455571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455581 : List Nat := [1, 4, 2, 1, 2, 1, 3, 1, 3, 5]
def baseStart_455581 : Nat := 118140960795 + 455581 * 2 ^ 59
def prefixEnd_455581 : Nat := 4983230072969 + 3 ^ 40 * 455581 * 2
def baseEnd_455581 : Nat := 77977343352029090314109

theorem tailTrace_455581 : CollatzResearch.WordTrace tailWord_455581 prefixEnd_455581 77977343352029090314109 := by
  unfold tailWord_455581
  simp only [CollatzResearch.WordTrace]
  refine ⟨16616404162515318885374597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11077602775010212590249731 16616404162515318885374597)
  ·
    refine ⟨3115575780471622291007737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16616404162515318885374597 3115575780471622291007737)
    ·
      refine ⟨2336681835353716718255803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3115575780471622291007737 2336681835353716718255803)
      ·
        refine ⟨3505022753030575077383705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2336681835353716718255803 3505022753030575077383705)
        ·
          refine ⟨2628767064772931308037779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3505022753030575077383705 2628767064772931308037779)
          ·
            refine ⟨3943150597159396962056669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2628767064772931308037779 3943150597159396962056669)
            ·
              refine ⟨1478681473934773860771251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3943150597159396962056669 1478681473934773860771251)
              ·
                refine ⟨2218022210902160791156877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1478681473934773860771251 2218022210902160791156877)
                ·
                  refine ⟨831758329088310296683829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2218022210902160791156877 831758329088310296683829)
                  ·
                    refine ⟨77977343352029090314109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 831758329088310296683829 77977343352029090314109)
                    ·
                      rfl

theorem cell23_455581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_455581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_455581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_455581 prefixEnd_455581 := by exact prefixLift 455581
  have htrace : WordTrace (prefixWord ++ tailWord_455581) baseStart_455581 baseEnd_455581 := by
    simpa [prefixWord, tailWord_455581, baseEnd_455581] using wordTrace_append hprefix tailTrace_455581
  have hstable : (prefixWord ++ tailWord_455581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455581).length < 2 ^ (prefixWord ++ tailWord_455581).sum := by decide
  have hdescent : baseEnd_455581 < baseStart_455581 := by decide
  rcases family_descends (prefixWord ++ tailWord_455581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455606 : List Nat := [5, 1, 4, 1, 1, 1, 1, 4, 1, 4]
def baseStart_455606 : Nat := 118140960795 + 455606 * 2 ^ 59
def prefixEnd_455606 : Nat := 4983230072969 + 3 ^ 40 * 455606 * 2
def baseEnd_455606 : Nat := 77981622357483224376571

theorem tailTrace_455606 : CollatzResearch.WordTrace tailWord_455606 prefixEnd_455606 77981622357483224376571 := by
  unfold tailWord_455606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1038582249214046759689667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11078210658283165436689781 1038582249214046759689667)
  ·
    refine ⟨1557873373821070139534501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1038582249214046759689667 1557873373821070139534501)
    ·
      refine ⟨292101257591450651162719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1557873373821070139534501 292101257591450651162719)
      ·
        refine ⟨438151886387175976744079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292101257591450651162719 438151886387175976744079)
        ·
          refine ⟨657227829580763965116119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438151886387175976744079 657227829580763965116119)
          ·
            refine ⟨985841744371145947674179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 657227829580763965116119 985841744371145947674179)
            ·
              refine ⟨1478762616556718921511269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 985841744371145947674179 1478762616556718921511269)
              ·
                refine ⟨277267990604384797783363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1478762616556718921511269 277267990604384797783363)
                ·
                  refine ⟨415901985906577196675045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 277267990604384797783363 415901985906577196675045)
                  ·
                    refine ⟨77981622357483224376571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 415901985906577196675045 77981622357483224376571)
                    ·
                      rfl

theorem cell23_455606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_455606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_455606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_455606 prefixEnd_455606 := by exact prefixLift 455606
  have htrace : WordTrace (prefixWord ++ tailWord_455606) baseStart_455606 baseEnd_455606 := by
    simpa [prefixWord, tailWord_455606, baseEnd_455606] using wordTrace_append hprefix tailTrace_455606
  have hstable : (prefixWord ++ tailWord_455606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455606).length < 2 ^ (prefixWord ++ tailWord_455606).sum := by decide
  have hdescent : baseEnd_455606 < baseStart_455606 := by decide
  rcases family_descends (prefixWord ++ tailWord_455606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455628 : List Nat := [2, 2, 1, 4, 1, 1, 1, 5, 2, 4]
def baseStart_455628 : Nat := 118140960795 + 455628 * 2 ^ 59
def prefixEnd_455628 : Nat := 4983230072969 + 3 ^ 40 * 455628 * 2
def baseEnd_455628 : Nat := 77985387882282862351537

theorem tailTrace_455628 : CollatzResearch.WordTrace tailWord_455628 prefixEnd_455628 77985387882282862351537 := by
  unfold tailWord_455628
  simp only [CollatzResearch.WordTrace]
  refine ⟨8309059196672522956167769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11078745595563363941557025 8309059196672522956167769)
  ·
    refine ⟨6231794397504392217125827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8309059196672522956167769 6231794397504392217125827)
    ·
      refine ⟨9347691596256588325688741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6231794397504392217125827 9347691596256588325688741)
      ·
        refine ⟨1752692174298110311066639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9347691596256588325688741 1752692174298110311066639)
        ·
          refine ⟨2629038261447165466599959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1752692174298110311066639 2629038261447165466599959)
          ·
            refine ⟨3943557392170748199899939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2629038261447165466599959 3943557392170748199899939)
            ·
              refine ⟨5915336088256122299849909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3943557392170748199899939 5915336088256122299849909)
              ·
                refine ⟨554562758274011465610929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5915336088256122299849909 554562758274011465610929)
                ·
                  refine ⟨415922068705508599208197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 554562758274011465610929 415922068705508599208197)
                  ·
                    refine ⟨77985387882282862351537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 415922068705508599208197 77985387882282862351537)
                    ·
                      rfl

theorem cell23_455628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 5, 2, 4].length) (baseStart_455628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_455628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_455628 prefixEnd_455628 := by exact prefixLift 455628
  have htrace : WordTrace (prefixWord ++ tailWord_455628) baseStart_455628 baseEnd_455628 := by
    simpa [prefixWord, tailWord_455628, baseEnd_455628] using wordTrace_append hprefix tailTrace_455628
  have hstable : (prefixWord ++ tailWord_455628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455628).length < 2 ^ (prefixWord ++ tailWord_455628).sum := by decide
  have hdescent : baseEnd_455628 < baseStart_455628 := by decide
  rcases family_descends (prefixWord ++ tailWord_455628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455631 : List Nat := [1, 1, 2, 1, 1, 6, 1, 3, 1, 2, 4]
def baseStart_455631 : Nat := 118140960795 + 455631 * 2 ^ 59
def prefixEnd_455631 : Nat := 4983230072969 + 3 ^ 40 * 455631 * 2
def baseEnd_455631 : Nat := 233957704088812075317097

theorem tailTrace_455631 : CollatzResearch.WordTrace tailWord_455631 prefixEnd_455631 233957704088812075317097 := by
  unfold tailWord_455631
  simp only [CollatzResearch.WordTrace]
  refine ⟨16618227812334177424694747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11078818541556118283129831 16618227812334177424694747)
  ·
    refine ⟨24927341718501266137042121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16618227812334177424694747 24927341718501266137042121)
    ·
      refine ⟨18695506288875949602781591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24927341718501266137042121 18695506288875949602781591)
      ·
        refine ⟨28043259433313924404172387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18695506288875949602781591 28043259433313924404172387)
        ·
          refine ⟨42064889149970886606258581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28043259433313924404172387 42064889149970886606258581)
          ·
            refine ⟨1971791678904885309668371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42064889149970886606258581 1971791678904885309668371)
            ·
              refine ⟨2957687518357327964502557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1971791678904885309668371 2957687518357327964502557)
              ·
                refine ⟨1109132819383997986688459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2957687518357327964502557 1109132819383997986688459)
                ·
                  refine ⟨1663699229075996980032689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1109132819383997986688459 1663699229075996980032689)
                  ·
                    refine ⟨1247774421806997735024517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1663699229075996980032689 1247774421806997735024517)
                    ·
                      refine ⟨233957704088812075317097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1247774421806997735024517 233957704088812075317097)
                      ·
                        rfl

theorem cell23_455631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 2, 4].length) (baseStart_455631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_455631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_455631 prefixEnd_455631 := by exact prefixLift 455631
  have htrace : WordTrace (prefixWord ++ tailWord_455631) baseStart_455631 baseEnd_455631 := by
    simpa [prefixWord, tailWord_455631, baseEnd_455631] using wordTrace_append hprefix tailTrace_455631
  have hstable : (prefixWord ++ tailWord_455631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455631).length < 2 ^ (prefixWord ++ tailWord_455631).sum := by decide
  have hdescent : baseEnd_455631 < baseStart_455631 := by decide
  rcases family_descends (prefixWord ++ tailWord_455631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455655 : List Nat := [1, 1, 5, 2, 2, 2, 1, 3, 1, 2, 3]
def baseStart_455655 : Nat := 118140960795 + 455655 * 2 ^ 59
def prefixEnd_455655 : Nat := 4983230072969 + 3 ^ 40 * 455655 * 2
def baseEnd_455655 : Nat := 233970027624519981416987

theorem tailTrace_455655 : CollatzResearch.WordTrace tailWord_455655 prefixEnd_455655 233970027624519981416987 := by
  unfold tailWord_455655
  simp only [CollatzResearch.WordTrace]
  refine ⟨16619103164247229523568419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11079402109498153015712279 16619103164247229523568419)
  ·
    refine ⟨24928654746370844285352629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16619103164247229523568419 24928654746370844285352629)
    ·
      refine ⟨2337061382472266651751809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24928654746370844285352629 2337061382472266651751809)
      ·
        refine ⟨1752796036854199988813857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2337061382472266651751809 1752796036854199988813857)
        ·
          refine ⟨1314597027640649991610393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1752796036854199988813857 1314597027640649991610393)
          ·
            refine ⟨985947770730487493707795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1314597027640649991610393 985947770730487493707795)
            ·
              refine ⟨1478921656095731240561693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 985947770730487493707795 1478921656095731240561693)
              ·
                refine ⟨554595621035899215210635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1478921656095731240561693 554595621035899215210635)
                ·
                  refine ⟨831893431553848822815953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 554595621035899215210635 831893431553848822815953)
                  ·
                    refine ⟨623920073665386617111965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 831893431553848822815953 623920073665386617111965)
                    ·
                      refine ⟨233970027624519981416987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 623920073665386617111965 233970027624519981416987)
                      ·
                        rfl

theorem cell23_455655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_455655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_455655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_455655 prefixEnd_455655 := by exact prefixLift 455655
  have htrace : WordTrace (prefixWord ++ tailWord_455655) baseStart_455655 baseEnd_455655 := by
    simpa [prefixWord, tailWord_455655, baseEnd_455655] using wordTrace_append hprefix tailTrace_455655
  have hstable : (prefixWord ++ tailWord_455655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455655).length < 2 ^ (prefixWord ++ tailWord_455655).sum := by decide
  have hdescent : baseEnd_455655 < baseStart_455655 := by decide
  rcases family_descends (prefixWord ++ tailWord_455655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455662 : List Nat := [4, 1, 2, 1, 4, 2, 1, 2, 2, 4]
def baseStart_455662 : Nat := 118140960795 + 455662 * 2 ^ 59
def prefixEnd_455662 : Nat := 4983230072969 + 3 ^ 40 * 455662 * 2
def baseEnd_455662 : Nat := 77991207329700484676485

theorem tailTrace_455662 : CollatzResearch.WordTrace tailWord_455662 prefixEnd_455662 77991207329700484676485 := by
  unfold tailWord_455662
  simp only [CollatzResearch.WordTrace]
  refine ⟨2077419809402733714884155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11079572316814579812715493 2077419809402733714884155)
  ·
    refine ⟨3116129714104100572326233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2077419809402733714884155 3116129714104100572326233)
    ·
      refine ⟨2337097285578075429244675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3116129714104100572326233 2337097285578075429244675)
      ·
        refine ⟨3505645928367113143867013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2337097285578075429244675 3505645928367113143867013)
        ·
          refine ⟨657308611568833714475065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3505645928367113143867013 657308611568833714475065)
          ·
            refine ⟨492981458676625285856299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 657308611568833714475065 492981458676625285856299)
            ·
              refine ⟨739472188014937928784449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 492981458676625285856299 739472188014937928784449)
              ·
                refine ⟨554604141011203446588337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 739472188014937928784449 554604141011203446588337)
                ·
                  refine ⟨415953105758402584941253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 554604141011203446588337 415953105758402584941253)
                  ·
                    refine ⟨77991207329700484676485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 415953105758402584941253 77991207329700484676485)
                    ·
                      rfl

theorem cell23_455662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_455662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_455662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_455662 prefixEnd_455662 := by exact prefixLift 455662
  have htrace : WordTrace (prefixWord ++ tailWord_455662) baseStart_455662 baseEnd_455662 := by
    simpa [prefixWord, tailWord_455662, baseEnd_455662] using wordTrace_append hprefix tailTrace_455662
  have hstable : (prefixWord ++ tailWord_455662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455662).length < 2 ^ (prefixWord ++ tailWord_455662).sum := by decide
  have hdescent : baseEnd_455662 < baseStart_455662 := by decide
  rcases family_descends (prefixWord ++ tailWord_455662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455711 : List Nat := [1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 5]
def baseStart_455711 : Nat := 118140960795 + 455711 * 2 ^ 59
def prefixEnd_455711 : Nat := 4983230072969 + 3 ^ 40 * 455711 * 2
def baseEnd_455711 : Nat := 233998782541171762316729

theorem tailTrace_455711 : CollatzResearch.WordTrace tailWord_455711 prefixEnd_455711 233998782541171762316729 := by
  unfold tailWord_455711
  simp only [CollatzResearch.WordTrace]
  refine ⟨16621145652044351087606987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11080763768029567391737991 16621145652044351087606987)
  ·
    refine ⟨24931718478066526631410481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16621145652044351087606987 24931718478066526631410481)
    ·
      refine ⟨18698788858549894973557861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24931718478066526631410481 18698788858549894973557861)
      ·
        refine ⟨3506022910978105307542099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18698788858549894973557861 3506022910978105307542099)
        ·
          refine ⟨5259034366467157961313149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3506022910978105307542099 5259034366467157961313149)
          ·
            refine ⟨1972137887425184235492431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5259034366467157961313149 1972137887425184235492431)
            ·
              refine ⟨2958206831137776353238647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1972137887425184235492431 2958206831137776353238647)
              ·
                refine ⟨4437310246706664529857971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2958206831137776353238647 4437310246706664529857971)
                ·
                  refine ⟨6655965370059996794786957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4437310246706664529857971 6655965370059996794786957)
                  ·
                    refine ⟨2495987013772498798045109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6655965370059996794786957 2495987013772498798045109)
                    ·
                      refine ⟨233998782541171762316729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2495987013772498798045109 233998782541171762316729)
                      ·
                        rfl

theorem cell23_455711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_455711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_455711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_455711 prefixEnd_455711 := by exact prefixLift 455711
  have htrace : WordTrace (prefixWord ++ tailWord_455711) baseStart_455711 baseEnd_455711 := by
    simpa [prefixWord, tailWord_455711, baseEnd_455711] using wordTrace_append hprefix tailTrace_455711
  have hstable : (prefixWord ++ tailWord_455711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455711).length < 2 ^ (prefixWord ++ tailWord_455711).sum := by decide
  have hdescent : baseEnd_455711 < baseStart_455711 := by decide
  rcases family_descends (prefixWord ++ tailWord_455711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455761 : List Nat := [1, 2, 2, 1, 3, 1, 2, 3, 1, 7]
def baseStart_455761 : Nat := 118140960795 + 455761 * 2 ^ 59
def prefixEnd_455761 : Nat := 4983230072969 + 3 ^ 40 * 455761 * 2
def baseEnd_455761 : Nat := 78008152191298855563833

theorem tailTrace_455761 : CollatzResearch.WordTrace tailWord_455761 prefixEnd_455761 78008152191298855563833 := by
  unfold tailWord_455761
  simp only [CollatzResearch.WordTrace]
  refine ⟨16622969301863209626927137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11081979534575473084618091 16622969301863209626927137)
  ·
    refine ⟨12467226976397407220195353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16622969301863209626927137 12467226976397407220195353)
    ·
      refine ⟨9350420232298055415146515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12467226976397407220195353 9350420232298055415146515)
      ·
        refine ⟨14025630348447083122719773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9350420232298055415146515 14025630348447083122719773)
        ·
          refine ⟨5259611380667656171019915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14025630348447083122719773 5259611380667656171019915)
          ·
            refine ⟨7889417071001484256529873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5259611380667656171019915 7889417071001484256529873)
            ·
              refine ⟨5917062803251113192397405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7889417071001484256529873 5917062803251113192397405)
              ·
                refine ⟨2218898551219167447149027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5917062803251113192397405 2218898551219167447149027)
                ·
                  refine ⟨3328347826828751170723541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2218898551219167447149027 3328347826828751170723541)
                  ·
                    refine ⟨78008152191298855563833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3328347826828751170723541 78008152191298855563833)
                    ·
                      rfl

theorem cell23_455761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 7].length) (baseStart_455761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_455761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_455761 prefixEnd_455761 := by exact prefixLift 455761
  have htrace : WordTrace (prefixWord ++ tailWord_455761) baseStart_455761 baseEnd_455761 := by
    simpa [prefixWord, tailWord_455761, baseEnd_455761] using wordTrace_append hprefix tailTrace_455761
  have hstable : (prefixWord ++ tailWord_455761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455761).length < 2 ^ (prefixWord ++ tailWord_455761).sum := by decide
  have hdescent : baseEnd_455761 < baseStart_455761 := by decide
  rcases family_descends (prefixWord ++ tailWord_455761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455808 : List Nat := [2, 1, 1, 2, 1, 3, 3, 1, 5, 4]
def baseStart_455808 : Nat := 118140960795 + 455808 * 2 ^ 59
def prefixEnd_455808 : Nat := 4983230072969 + 3 ^ 40 * 455808 * 2
def baseEnd_455808 : Nat := 78016196721552627601261

theorem tailTrace_455808 : CollatzResearch.WordTrace tailWord_455808 prefixEnd_455808 78016196721552627601261 := by
  unfold tailWord_455808
  simp only [CollatzResearch.WordTrace]
  refine ⟨8312341766346468326944039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11083122355128624435925385 8312341766346468326944039)
  ·
    refine ⟨12468512649519702490416059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8312341766346468326944039 12468512649519702490416059)
    ·
      refine ⟨18702768974279553735624089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12468512649519702490416059 18702768974279553735624089)
      ·
        refine ⟨14027076730709665301718067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18702768974279553735624089 14027076730709665301718067)
        ·
          refine ⟨21040615096064497952577101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14027076730709665301718067 21040615096064497952577101)
          ·
            refine ⟨7890230661024186732216413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21040615096064497952577101 7890230661024186732216413)
            ·
              refine ⟨2958836497884070024581155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7890230661024186732216413 2958836497884070024581155)
              ·
                refine ⟨4438254746826105036871733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2958836497884070024581155 4438254746826105036871733)
                ·
                  refine ⟨416086382514947347206725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4438254746826105036871733 416086382514947347206725)
                  ·
                    refine ⟨78016196721552627601261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 416086382514947347206725 78016196721552627601261)
                    ·
                      rfl

theorem cell23_455808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 5, 4].length) (baseStart_455808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_455808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_455808 prefixEnd_455808 := by exact prefixLift 455808
  have htrace : WordTrace (prefixWord ++ tailWord_455808) baseStart_455808 baseEnd_455808 := by
    simpa [prefixWord, tailWord_455808, baseEnd_455808] using wordTrace_append hprefix tailTrace_455808
  have hstable : (prefixWord ++ tailWord_455808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455808).length < 2 ^ (prefixWord ++ tailWord_455808).sum := by decide
  have hdescent : baseEnd_455808 < baseStart_455808 := by decide
  rcases family_descends (prefixWord ++ tailWord_455808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455876 : List Nat := [2, 3, 3, 1, 3, 2, 1, 3, 1, 4]
def baseStart_455876 : Nat := 118140960795 + 455876 * 2 ^ 59
def prefixEnd_455876 : Nat := 4983230072969 + 3 ^ 40 * 455876 * 2
def baseEnd_455876 : Nat := 78027835616387872251157

theorem tailTrace_455876 : CollatzResearch.WordTrace tailWord_455876 prefixEnd_455876 78027835616387872251157 := by
  unfold tailWord_455876
  simp only [CollatzResearch.WordTrace]
  refine ⟨8313581848223292133681741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11084775797631056178242321 8313581848223292133681741)
  ·
    refine ⟨3117593193083734550130653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8313581848223292133681741 3117593193083734550130653)
    ·
      refine ⟨1169097447406400456298995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3117593193083734550130653 1169097447406400456298995)
      ·
        refine ⟨1753646171109600684448493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1169097447406400456298995 1753646171109600684448493)
        ·
          refine ⟨657617314166100256668185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1753646171109600684448493 657617314166100256668185)
          ·
            refine ⟨493212985624575192501139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 657617314166100256668185 493212985624575192501139)
            ·
              refine ⟨739819478436862788751709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 493212985624575192501139 739819478436862788751709)
              ·
                refine ⟨277432304413823545781891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 739819478436862788751709 277432304413823545781891)
                ·
                  refine ⟨416148456620735318672837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 277432304413823545781891 416148456620735318672837)
                  ·
                    refine ⟨78027835616387872251157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 416148456620735318672837 78027835616387872251157)
                    ·
                      rfl

theorem cell23_455876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_455876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_455876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_455876 prefixEnd_455876 := by exact prefixLift 455876
  have htrace : WordTrace (prefixWord ++ tailWord_455876) baseStart_455876 baseEnd_455876 := by
    simpa [prefixWord, tailWord_455876, baseEnd_455876] using wordTrace_append hprefix tailTrace_455876
  have hstable : (prefixWord ++ tailWord_455876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455876).length < 2 ^ (prefixWord ++ tailWord_455876).sum := by decide
  have hdescent : baseEnd_455876 < baseStart_455876 := by decide
  rcases family_descends (prefixWord ++ tailWord_455876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455919 : List Nat := [1, 1, 2, 1, 8, 1, 1, 2, 1, 5]
def baseStart_455919 : Nat := 118140960795 + 455919 * 2 ^ 59
def prefixEnd_455919 : Nat := 4983230072969 + 3 ^ 40 * 455919 * 2
def baseEnd_455919 : Nat := 78035195505768982838591

theorem tailTrace_455919 : CollatzResearch.WordTrace tailWord_455919 prefixEnd_455919 78035195505768982838591 := by
  unfold tailWord_455919
  simp only [CollatzResearch.WordTrace]
  refine ⟨16628732035290802611178811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11085821356860535074119207 16628732035290802611178811)
  ·
    refine ⟨24943098052936203916768217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16628732035290802611178811 24943098052936203916768217)
    ·
      refine ⟨18707323539702152937576163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24943098052936203916768217 18707323539702152937576163)
      ·
        refine ⟨28060985309553229406364245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18707323539702152937576163 28060985309553229406364245)
        ·
          refine ⟨328839671596326907105831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 28060985309553229406364245 328839671596326907105831)
          ·
            refine ⟨493259507394490360658747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328839671596326907105831 493259507394490360658747)
            ·
              refine ⟨739889261091735540988121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 493259507394490360658747 739889261091735540988121)
              ·
                refine ⟨554916945818801655741091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 739889261091735540988121 554916945818801655741091)
                ·
                  refine ⟨832375418728202483611637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 554916945818801655741091 832375418728202483611637)
                  ·
                    refine ⟨78035195505768982838591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 832375418728202483611637 78035195505768982838591)
                    ·
                      rfl

theorem cell23_455919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 2, 1, 5].length) (baseStart_455919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_455919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_455919 prefixEnd_455919 := by exact prefixLift 455919
  have htrace : WordTrace (prefixWord ++ tailWord_455919) baseStart_455919 baseEnd_455919 := by
    simpa [prefixWord, tailWord_455919, baseEnd_455919] using wordTrace_append hprefix tailTrace_455919
  have hstable : (prefixWord ++ tailWord_455919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455919).length < 2 ^ (prefixWord ++ tailWord_455919).sum := by decide
  have hdescent : baseEnd_455919 < baseStart_455919 := by decide
  rcases family_descends (prefixWord ++ tailWord_455919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455922 : List Nat := [3, 2, 1, 3, 3, 1, 1, 1, 3, 1, 4]
def baseStart_455922 : Nat := 118140960795 + 455922 * 2 ^ 59
def prefixEnd_455922 : Nat := 4983230072969 + 3 ^ 40 * 455922 * 2
def baseEnd_455922 : Nat := 234107126959270436778259

theorem tailTrace_455922 : CollatzResearch.WordTrace tailWord_455922 prefixEnd_455922 234107126959270436778259 := by
  unfold tailWord_455922
  simp only [CollatzResearch.WordTrace]
  refine ⟨4157210363569983530884505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11085894302853289415692013 4157210363569983530884505)
  ·
    refine ⟨3117907772677487648163379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4157210363569983530884505 3117907772677487648163379)
    ·
      refine ⟨4676861659016231472245069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3117907772677487648163379 4676861659016231472245069)
      ·
        refine ⟨1753823122131086802091901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4676861659016231472245069 1753823122131086802091901)
        ·
          refine ⟨657683670799157550784463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1753823122131086802091901 657683670799157550784463)
          ·
            refine ⟨986525506198736326176695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 657683670799157550784463 986525506198736326176695)
            ·
              refine ⟨1479788259298104489265043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 986525506198736326176695 1479788259298104489265043)
              ·
                refine ⟨2219682388947156733897565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1479788259298104489265043 2219682388947156733897565)
                ·
                  refine ⟨832380895855183775211587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2219682388947156733897565 832380895855183775211587)
                  ·
                    refine ⟨1248571343782775662817381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 832380895855183775211587 1248571343782775662817381)
                    ·
                      refine ⟨234107126959270436778259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1248571343782775662817381 234107126959270436778259)
                      ·
                        rfl

theorem cell23_455922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_455922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_455922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_455922 prefixEnd_455922 := by exact prefixLift 455922
  have htrace : WordTrace (prefixWord ++ tailWord_455922) baseStart_455922 baseEnd_455922 := by
    simpa [prefixWord, tailWord_455922, baseEnd_455922] using wordTrace_append hprefix tailTrace_455922
  have hstable : (prefixWord ++ tailWord_455922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455922).length < 2 ^ (prefixWord ++ tailWord_455922).sum := by decide
  have hdescent : baseEnd_455922 < baseStart_455922 := by decide
  rcases family_descends (prefixWord ++ tailWord_455922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455935 : List Nat := [1, 1, 2, 2, 1, 6, 1, 2, 1, 2, 4]
def baseStart_455935 : Nat := 118140960795 + 455935 * 2 ^ 59
def prefixEnd_455935 : Nat := 4983230072969 + 3 ^ 40 * 455935 * 2
def baseEnd_455935 : Nat := 234113802207778885915699

theorem tailTrace_455935 : CollatzResearch.WordTrace tailWord_455935 prefixEnd_455935 234113802207778885915699 := by
  unfold tailWord_455935
  simp only [CollatzResearch.WordTrace]
  refine ⟨16629315603232837343761259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11086210402155224895840839 16629315603232837343761259)
  ·
    refine ⟨24943973404849256015641889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16629315603232837343761259 24943973404849256015641889)
    ·
      refine ⟨18707980053636942011731417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24943973404849256015641889 18707980053636942011731417)
      ·
        refine ⟨14030985040227706508798563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18707980053636942011731417 14030985040227706508798563)
        ·
          refine ⟨21046477560341559763197845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14030985040227706508798563 21046477560341559763197845)
          ·
            refine ⟨986553635641010613899899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21046477560341559763197845 986553635641010613899899)
            ·
              refine ⟨1479830453461515920849849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 986553635641010613899899 1479830453461515920849849)
              ·
                refine ⟨1109872840096136940637387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1479830453461515920849849 1109872840096136940637387)
                ·
                  refine ⟨1664809260144205410956081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1109872840096136940637387 1664809260144205410956081)
                  ·
                    refine ⟨1248606945108154058217061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1664809260144205410956081 1248606945108154058217061)
                    ·
                      refine ⟨234113802207778885915699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1248606945108154058217061 234113802207778885915699)
                      ·
                        rfl

theorem cell23_455935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 2, 4].length) (baseStart_455935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_455935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_455935 prefixEnd_455935 := by exact prefixLift 455935
  have htrace : WordTrace (prefixWord ++ tailWord_455935) baseStart_455935 baseEnd_455935 := by
    simpa [prefixWord, tailWord_455935, baseEnd_455935] using wordTrace_append hprefix tailTrace_455935
  have hstable : (prefixWord ++ tailWord_455935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455935).length < 2 ^ (prefixWord ++ tailWord_455935).sum := by decide
  have hdescent : baseEnd_455935 < baseStart_455935 := by decide
  rcases family_descends (prefixWord ++ tailWord_455935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455972 : List Nat := [2, 3, 1, 3, 1, 1, 4, 1, 1, 3, 3]
def baseStart_455972 : Nat := 118140960795 + 455972 * 2 ^ 59
def prefixEnd_455972 : Nat := 4983230072969 + 3 ^ 40 * 455972 * 2
def baseEnd_455972 : Nat := 234132800991995241153029

theorem tailTrace_455972 : CollatzResearch.WordTrace tailWord_455972 prefixEnd_455972 234132800991995241153029 := by
  unfold tailWord_455972
  simp only [CollatzResearch.WordTrace]
  refine ⟨8315332552049396331429085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11087110069399195108572113 8315332552049396331429085)
  ·
    refine ⟨3118249707018523624285907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8315332552049396331429085 3118249707018523624285907)
    ·
      refine ⟨4677374560527785436428861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3118249707018523624285907 4677374560527785436428861)
      ·
        refine ⟨1754015460197919538660823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4677374560527785436428861 1754015460197919538660823)
        ·
          refine ⟨2631023190296879307991235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1754015460197919538660823 2631023190296879307991235)
          ·
            refine ⟨3946534785445318961986853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2631023190296879307991235 3946534785445318961986853)
            ·
              refine ⟨739975272270997305372535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3946534785445318961986853 739975272270997305372535)
              ·
                refine ⟨1109962908406495958058803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 739975272270997305372535 1109962908406495958058803)
                ·
                  refine ⟨1664944362609743937088205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1109962908406495958058803 1664944362609743937088205)
                  ·
                    refine ⟨624354135978653976408077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1664944362609743937088205 624354135978653976408077)
                    ·
                      refine ⟨234132800991995241153029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 624354135978653976408077 234132800991995241153029)
                      ·
                        rfl

theorem cell23_455972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_455972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_455972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_455972 prefixEnd_455972 := by exact prefixLift 455972
  have htrace : WordTrace (prefixWord ++ tailWord_455972) baseStart_455972 baseEnd_455972 := by
    simpa [prefixWord, tailWord_455972, baseEnd_455972] using wordTrace_append hprefix tailTrace_455972
  have hstable : (prefixWord ++ tailWord_455972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455972).length < 2 ^ (prefixWord ++ tailWord_455972).sum := by decide
  have hdescent : baseEnd_455972 < baseStart_455972 := by decide
  rcases family_descends (prefixWord ++ tailWord_455972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455990 : List Nat := [5, 1, 2, 3, 2, 1, 2, 1, 1, 1, 4]
def baseStart_455990 : Nat := 118140960795 + 455990 * 2 ^ 59
def prefixEnd_455990 : Nat := 4983230072969 + 3 ^ 40 * 455990 * 2
def baseEnd_455990 : Nat := 234142043643776170727947

theorem tailTrace_455990 : CollatzResearch.WordTrace tailWord_455990 prefixEnd_455990 234142043643776170727947 := by
  unfold tailWord_455990
  simp only [CollatzResearch.WordTrace]
  refine ⟨1039457601127098858563339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11087547745355721158008949 1039457601127098858563339)
  ·
    refine ⟨1559186401690648287845009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1039457601127098858563339 1559186401690648287845009)
    ·
      refine ⟨1169389801267986215883757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1559186401690648287845009 1169389801267986215883757)
      ·
        refine ⟨438521175475494830956409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1169389801267986215883757 438521175475494830956409)
        ·
          refine ⟨328890881606621123217307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 438521175475494830956409 328890881606621123217307)
          ·
            refine ⟨493336322409931684825961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328890881606621123217307 493336322409931684825961)
            ·
              refine ⟨370002241807448763619471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 493336322409931684825961 370002241807448763619471)
              ·
                refine ⟨555003362711173145429207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 370002241807448763619471 555003362711173145429207)
                ·
                  refine ⟨832505044066759718143811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 555003362711173145429207 832505044066759718143811)
                  ·
                    refine ⟨1248757566100139577215717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 832505044066759718143811 1248757566100139577215717)
                    ·
                      refine ⟨234142043643776170727947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1248757566100139577215717 234142043643776170727947)
                      ·
                        rfl

theorem cell23_455990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_455990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_455990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_455990 prefixEnd_455990 := by exact prefixLift 455990
  have htrace : WordTrace (prefixWord ++ tailWord_455990) baseStart_455990 baseEnd_455990 := by
    simpa [prefixWord, tailWord_455990, baseEnd_455990] using wordTrace_append hprefix tailTrace_455990
  have hstable : (prefixWord ++ tailWord_455990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455990).length < 2 ^ (prefixWord ++ tailWord_455990).sum := by decide
  have hdescent : baseEnd_455990 < baseStart_455990 := by decide
  rcases family_descends (prefixWord ++ tailWord_455990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455993 : List Nat := [1, 2, 1, 6, 3, 1, 2, 1, 1, 2, 3]
def baseStart_455993 : Nat := 118140960795 + 455993 * 2 ^ 59
def prefixEnd_455993 : Nat := 4983230072969 + 3 ^ 40 * 455993 * 2
def baseEnd_455993 : Nat := 234143584085739658990433

theorem tailTrace_455993 : CollatzResearch.WordTrace tailWord_455993 prefixEnd_455993 234143584085739658990433 := by
  unfold tailWord_455993
  simp only [CollatzResearch.WordTrace]
  refine ⟨16631431037022713249372633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11087620691348475499581755 16631431037022713249372633)
  ·
    refine ⟨12473573277767034937029475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16631431037022713249372633 12473573277767034937029475)
    ·
      refine ⟨18710359916650552405544213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12473573277767034937029475 18710359916650552405544213)
      ·
        refine ⟨877048121092994644009885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18710359916650552405544213 877048121092994644009885)
        ·
          refine ⟨328893045409872991503707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 877048121092994644009885 328893045409872991503707)
          ·
            refine ⟨493339568114809487255561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328893045409872991503707 493339568114809487255561)
            ·
              refine ⟨370004676086107115441671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 493339568114809487255561 370004676086107115441671)
              ·
                refine ⟨555007014129160673162507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 370004676086107115441671 555007014129160673162507)
                ·
                  refine ⟨832510521193741009743761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 555007014129160673162507 832510521193741009743761)
                  ·
                    refine ⟨624382890895305757307821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 832510521193741009743761 624382890895305757307821)
                    ·
                      refine ⟨234143584085739658990433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 624382890895305757307821 234143584085739658990433)
                      ·
                        rfl

theorem cell23_455993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_455993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_455993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_455993 prefixEnd_455993 := by exact prefixLift 455993
  have htrace : WordTrace (prefixWord ++ tailWord_455993) baseStart_455993 baseEnd_455993 := by
    simpa [prefixWord, tailWord_455993, baseEnd_455993] using wordTrace_append hprefix tailTrace_455993
  have hstable : (prefixWord ++ tailWord_455993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455993).length < 2 ^ (prefixWord ++ tailWord_455993).sum := by decide
  have hdescent : baseEnd_455993 < baseStart_455993 := by decide
  rcases family_descends (prefixWord ++ tailWord_455993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455995 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 4, 8, 2]
def baseStart_455995 : Nat := 118140960795 + 455995 * 2 ^ 59
def prefixEnd_455995 : Nat := 4983230072969 + 3 ^ 40 * 455995 * 2
def baseEnd_455995 : Nat := 234144611047048651165423

theorem tailTrace_455995 : CollatzResearch.WordTrace tailWord_455995 prefixEnd_455995 234144611047048651165423 := by
  unfold tailWord_455995
  simp only [CollatzResearch.WordTrace]
  refine ⟨16631503983015467590945439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11087669322010311727296959 16631503983015467590945439)
  ·
    refine ⟨24947255974523201386418159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16631503983015467590945439 24947255974523201386418159)
    ·
      refine ⟨37420883961784802079627239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24947255974523201386418159 37420883961784802079627239)
      ·
        refine ⟨56131325942677203119440859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37420883961784802079627239 56131325942677203119440859)
        ·
          refine ⟨84196988914015804679161289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56131325942677203119440859 84196988914015804679161289)
          ·
            refine ⟨63147741685511853509370967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84196988914015804679161289 63147741685511853509370967)
            ·
              refine ⟨94721612528267780264056451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63147741685511853509370967 94721612528267780264056451)
              ·
                refine ⟨142082418792401670396084677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94721612528267780264056451 142082418792401670396084677)
                ·
                  refine ⟨26640453523575313199265877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142082418792401670396084677 26640453523575313199265877)
                  ·
                    refine ⟨312192814729398201553897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 26640453523575313199265877 312192814729398201553897)
                    ·
                      refine ⟨234144611047048651165423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 312192814729398201553897 234144611047048651165423)
                      ·
                        rfl

theorem cell23_455995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 8, 2].length) (baseStart_455995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_455995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_455995 prefixEnd_455995 := by exact prefixLift 455995
  have htrace : WordTrace (prefixWord ++ tailWord_455995) baseStart_455995 baseEnd_455995 := by
    simpa [prefixWord, tailWord_455995, baseEnd_455995] using wordTrace_append hprefix tailTrace_455995
  have hstable : (prefixWord ++ tailWord_455995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455995).length < 2 ^ (prefixWord ++ tailWord_455995).sum := by decide
  have hdescent : baseEnd_455995 < baseStart_455995 := by decide
  rcases family_descends (prefixWord ++ tailWord_455995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455999 : List Nat := [1, 1, 2, 2, 4, 3, 1, 3, 1, 3, 2]
def baseStart_455999 : Nat := 118140960795 + 455999 * 2 ^ 59
def prefixEnd_455999 : Nat := 4983230072969 + 3 ^ 40 * 455999 * 2
def baseEnd_455999 : Nat := 234146664969666635515405

theorem tailTrace_455999 : CollatzResearch.WordTrace tailWord_455999 prefixEnd_455999 234146664969666635515405 := by
  unfold tailWord_455999
  simp only [CollatzResearch.WordTrace]
  refine ⟨16631649875000976274091051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11087766583333984182727367 16631649875000976274091051)
  ·
    refine ⟨24947474812501464411136577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16631649875000976274091051 24947474812501464411136577)
    ·
      refine ⟨18710606109376098308352433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24947474812501464411136577 18710606109376098308352433)
      ·
        refine ⟨14032954582032073731264325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18710606109376098308352433 14032954582032073731264325)
        ·
          refine ⟨2631178984131013824612061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14032954582032073731264325 2631178984131013824612061)
          ·
            refine ⟨986692119049130184229523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2631178984131013824612061 986692119049130184229523)
            ·
              refine ⟨1480038178573695276344285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 986692119049130184229523 1480038178573695276344285)
              ·
                refine ⟨555014316965135728629107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1480038178573695276344285 555014316965135728629107)
                ·
                  refine ⟨832521475447703592943661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 555014316965135728629107 832521475447703592943661)
                  ·
                    refine ⟨312195553292888847353873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 832521475447703592943661 312195553292888847353873)
                    ·
                      refine ⟨234146664969666635515405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 312195553292888847353873 234146664969666635515405)
                      ·
                        rfl

theorem cell23_455999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 3, 1, 3, 2].length) (baseStart_455999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_455999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_455999 prefixEnd_455999 := by exact prefixLift 455999
  have htrace : WordTrace (prefixWord ++ tailWord_455999) baseStart_455999 baseEnd_455999 := by
    simpa [prefixWord, tailWord_455999, baseEnd_455999] using wordTrace_append hprefix tailTrace_455999
  have hstable : (prefixWord ++ tailWord_455999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455999).length < 2 ^ (prefixWord ++ tailWord_455999).sum := by decide
  have hdescent : baseEnd_455999 < baseStart_455999 := by decide
  rcases family_descends (prefixWord ++ tailWord_455999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456025 : List Nat := [1, 2, 1, 2, 2, 2, 4, 1, 2, 2, 4]
def baseStart_456025 : Nat := 118140960795 + 456025 * 2 ^ 59
def prefixEnd_456025 : Nat := 4983230072969 + 3 ^ 40 * 456025 * 2
def baseEnd_456025 : Nat := 234160015466683533790285

theorem tailTrace_456025 : CollatzResearch.WordTrace tailWord_456025 prefixEnd_456025 234160015466683533790285 := by
  unfold tailWord_456025
  simp only [CollatzResearch.WordTrace]
  refine ⟨16632598172906782714537529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11088398781937855143025019 16632598172906782714537529)
  ·
    refine ⟨12474448629680087035903147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16632598172906782714537529 12474448629680087035903147)
    ·
      refine ⟨18711672944520130553854721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12474448629680087035903147 18711672944520130553854721)
      ·
        refine ⟨14033754708390097915391041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18711672944520130553854721 14033754708390097915391041)
        ·
          refine ⟨10525316031292573436543281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14033754708390097915391041 10525316031292573436543281)
          ·
            refine ⟨7893987023469430077407461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10525316031292573436543281 7893987023469430077407461)
            ·
              refine ⟨1480122566900518139513899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7893987023469430077407461 1480122566900518139513899)
              ·
                refine ⟨2220183850350777209270849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1480122566900518139513899 2220183850350777209270849)
                ·
                  refine ⟨1665137887763082906953137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2220183850350777209270849 1665137887763082906953137)
                  ·
                    refine ⟨1248853415822312180214853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1665137887763082906953137 1248853415822312180214853)
                    ·
                      refine ⟨234160015466683533790285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1248853415822312180214853 234160015466683533790285)
                      ·
                        rfl

theorem cell23_456025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 2, 4].length) (baseStart_456025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456025 prefixEnd_456025 := by exact prefixLift 456025
  have htrace : WordTrace (prefixWord ++ tailWord_456025) baseStart_456025 baseEnd_456025 := by
    simpa [prefixWord, tailWord_456025, baseEnd_456025] using wordTrace_append hprefix tailTrace_456025
  have hstable : (prefixWord ++ tailWord_456025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456025).length < 2 ^ (prefixWord ++ tailWord_456025).sum := by decide
  have hdescent : baseEnd_456025 < baseStart_456025 := by decide
  rcases family_descends (prefixWord ++ tailWord_456025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456035 : List Nat := [1, 1, 1, 5, 2, 2, 2, 2, 7]
def baseStart_456035 : Nat := 118140960795 + 456035 * 2 ^ 59
def prefixEnd_456035 : Nat := 4983230072969 + 3 ^ 40 * 456035 * 2
def baseEnd_456035 : Nat := 26018350030358721629471

theorem tailTrace_456035 : CollatzResearch.WordTrace tailWord_456035 prefixEnd_456035 26018350030358721629471 := by
  unfold tailWord_456035
  simp only [CollatzResearch.WordTrace]
  refine ⟨16632962902870554422401559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11088641935247036281601039 16632962902870554422401559)
  ·
    refine ⟨24949444354305831633602339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16632962902870554422401559 24949444354305831633602339)
    ·
      refine ⟨37424166531458747450403509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24949444354305831633602339 37424166531458747450403509)
      ·
        refine ⟨3508515612324257573475329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37424166531458747450403509 3508515612324257573475329)
        ·
          refine ⟨2631386709243193180106497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3508515612324257573475329 2631386709243193180106497)
          ·
            refine ⟨1973540031932394885079873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2631386709243193180106497 1973540031932394885079873)
            ·
              refine ⟨1480155023949296163809905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1973540031932394885079873 1480155023949296163809905)
              ·
                refine ⟨1110116267961972122857429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1480155023949296163809905 1110116267961972122857429)
                ·
                  refine ⟨26018350030358721629471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1110116267961972122857429 26018350030358721629471)
                  ·
                    rfl

theorem cell23_456035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 7].length) (baseStart_456035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456035 prefixEnd_456035 := by exact prefixLift 456035
  have htrace : WordTrace (prefixWord ++ tailWord_456035) baseStart_456035 baseEnd_456035 := by
    simpa [prefixWord, tailWord_456035, baseEnd_456035] using wordTrace_append hprefix tailTrace_456035
  have hstable : (prefixWord ++ tailWord_456035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456035).length < 2 ^ (prefixWord ++ tailWord_456035).sum := by decide
  have hdescent : baseEnd_456035 < baseStart_456035 := by decide
  rcases family_descends (prefixWord ++ tailWord_456035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456075 : List Nat := [1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 5]
def baseStart_456075 : Nat := 118140960795 + 456075 * 2 ^ 59
def prefixEnd_456075 : Nat := 4983230072969 + 3 ^ 40 * 456075 * 2
def baseEnd_456075 : Nat := 234185689499408338165055

theorem tailTrace_456075 : CollatzResearch.WordTrace tailWord_456075 prefixEnd_456075 234185689499408338165055 := by
  unfold tailWord_456075
  simp only [CollatzResearch.WordTrace]
  refine ⟨16634421822725641253857679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11089614548483760835905119 16634421822725641253857679)
  ·
    refine ⟨24951632734088461880786519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16634421822725641253857679 24951632734088461880786519)
    ·
      refine ⟨37427449101132692821179779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24951632734088461880786519 37427449101132692821179779)
      ·
        refine ⟨56141173651699039231769669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37427449101132692821179779 56141173651699039231769669)
        ·
          refine ⟨10526470059693569855956813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56141173651699039231769669 10526470059693569855956813)
          ·
            refine ⟨3947426272385088695983805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10526470059693569855956813 3947426272385088695983805)
            ·
              refine ⟨1480284852144408260993927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3947426272385088695983805 1480284852144408260993927)
              ·
                refine ⟨2220427278216612391490891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1480284852144408260993927 2220427278216612391490891)
                ·
                  refine ⟨3330640917324918587236337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2220427278216612391490891 3330640917324918587236337)
                  ·
                    refine ⟨2497980687993688940427253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3330640917324918587236337 2497980687993688940427253)
                    ·
                      refine ⟨234185689499408338165055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2497980687993688940427253 234185689499408338165055)
                      ·
                        rfl

theorem cell23_456075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 5].length) (baseStart_456075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456075 prefixEnd_456075 := by exact prefixLift 456075
  have htrace : WordTrace (prefixWord ++ tailWord_456075) baseStart_456075 baseEnd_456075 := by
    simpa [prefixWord, tailWord_456075, baseEnd_456075] using wordTrace_append hprefix tailTrace_456075
  have hstable : (prefixWord ++ tailWord_456075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456075).length < 2 ^ (prefixWord ++ tailWord_456075).sum := by decide
  have hdescent : baseEnd_456075 < baseStart_456075 := by decide
  rcases family_descends (prefixWord ++ tailWord_456075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456085 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 3, 3, 4]
def baseStart_456085 : Nat := 118140960795 + 456085 * 2 ^ 59
def prefixEnd_456085 : Nat := 4983230072969 + 3 ^ 40 * 456085 * 2
def baseEnd_456085 : Nat := 234190824305953299040009

theorem tailTrace_456085 : CollatzResearch.WordTrace tailWord_456085 prefixEnd_456085 234190824305953299040009 := by
  unfold tailWord_456085
  simp only [CollatzResearch.WordTrace]
  refine ⟨16634786552689412961721709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11089857701792941974481139 16634786552689412961721709)
  ·
    refine ⟨6238044957258529860645641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16634786552689412961721709 6238044957258529860645641)
    ·
      refine ⟨4678533717943897395484231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6238044957258529860645641 4678533717943897395484231)
      ·
        refine ⟨7017800576915846093226347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4678533717943897395484231 7017800576915846093226347)
        ·
          refine ⟨10526700865373769139839521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7017800576915846093226347 10526700865373769139839521)
          ·
            refine ⟨7895025649030326854879641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10526700865373769139839521 7895025649030326854879641)
            ·
              refine ⟨5921269236772745141159731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7895025649030326854879641 5921269236772745141159731)
              ·
                refine ⟨8881903855159117711739597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5921269236772745141159731 8881903855159117711739597)
                ·
                  refine ⟨3330713945684669141902349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8881903855159117711739597 3330713945684669141902349)
                  ·
                    refine ⟨1249017729631750928213381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3330713945684669141902349 1249017729631750928213381)
                    ·
                      refine ⟨234190824305953299040009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1249017729631750928213381 234190824305953299040009)
                      ·
                        rfl

theorem cell23_456085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_456085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456085 prefixEnd_456085 := by exact prefixLift 456085
  have htrace : WordTrace (prefixWord ++ tailWord_456085) baseStart_456085 baseEnd_456085 := by
    simpa [prefixWord, tailWord_456085, baseEnd_456085] using wordTrace_append hprefix tailTrace_456085
  have hstable : (prefixWord ++ tailWord_456085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456085).length < 2 ^ (prefixWord ++ tailWord_456085).sum := by decide
  have hdescent : baseEnd_456085 < baseStart_456085 := by decide
  rcases family_descends (prefixWord ++ tailWord_456085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456130 : List Nat := [3, 5, 2, 1, 1, 1, 1, 1, 2, 3, 3]
def baseStart_456130 : Nat := 118140960795 + 456130 * 2 ^ 59
def prefixEnd_456130 : Nat := 4983230072969 + 3 ^ 40 * 456130 * 2
def baseEnd_456130 : Nat := 234213930935405622977303

theorem tailTrace_456130 : CollatzResearch.WordTrace tailWord_456130 prefixEnd_456130 234213930935405622977303 := by
  unfold tailWord_456130
  simp only [CollatzResearch.WordTrace]
  refine ⟨4159106959381596411777461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11090951891684257098073229 4159106959381596411777461)
  ·
    refine ⟨389916277442024663604137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4159106959381596411777461 389916277442024663604137)
    ·
      refine ⟨292437208081518497703103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389916277442024663604137 292437208081518497703103)
      ·
        refine ⟨438655812122277746554655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292437208081518497703103 438655812122277746554655)
        ·
          refine ⟨657983718183416619831983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438655812122277746554655 657983718183416619831983)
          ·
            refine ⟨986975577275124929747975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 657983718183416619831983 986975577275124929747975)
            ·
              refine ⟨1480463365912687394621963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 986975577275124929747975 1480463365912687394621963)
              ·
                refine ⟨2220695048869031091932945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1480463365912687394621963 2220695048869031091932945)
                ·
                  refine ⟨1665521286651773318949709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2220695048869031091932945 1665521286651773318949709)
                  ·
                    refine ⟨624570482494414994606141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1665521286651773318949709 624570482494414994606141)
                    ·
                      refine ⟨234213930935405622977303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 624570482494414994606141 234213930935405622977303)
                      ·
                        rfl

theorem cell23_456130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_456130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456130 prefixEnd_456130 := by exact prefixLift 456130
  have htrace : WordTrace (prefixWord ++ tailWord_456130) baseStart_456130 baseEnd_456130 := by
    simpa [prefixWord, tailWord_456130, baseEnd_456130] using wordTrace_append hprefix tailTrace_456130
  have hstable : (prefixWord ++ tailWord_456130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456130).length < 2 ^ (prefixWord ++ tailWord_456130).sum := by decide
  have hdescent : baseEnd_456130 < baseStart_456130 := by decide
  rcases family_descends (prefixWord ++ tailWord_456130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456142 : List Nat := [4, 1, 1, 1, 2, 1, 4, 3, 6]
def baseStart_456142 : Nat := 118140960795 + 456142 * 2 ^ 59
def prefixEnd_456142 : Nat := 4983230072969 + 3 ^ 40 * 456142 * 2
def baseEnd_456142 : Nat := 26024454744806619558583

theorem tailTrace_456142 : CollatzResearch.WordTrace tailWord_456142 prefixEnd_456142 26024454744806619558583 := by
  unfold tailWord_456142
  simp only [CollatzResearch.WordTrace]
  refine ⟨2079608189185363962068335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11091243675655274464364453 2079608189185363962068335)
  ·
    refine ⟨3119412283778045943102503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2079608189185363962068335 3119412283778045943102503)
    ·
      refine ⟨4679118425667068914653755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3119412283778045943102503 4679118425667068914653755)
      ·
        refine ⟨7018677638500603371980633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4679118425667068914653755 7018677638500603371980633)
        ·
          refine ⟨5264008228875452528985475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7018677638500603371980633 5264008228875452528985475)
          ·
            refine ⟨7896012343313178793478213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5264008228875452528985475 7896012343313178793478213)
            ·
              refine ⟨1480502314371221023777165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7896012343313178793478213 1480502314371221023777165)
              ·
                refine ⟨555188367889207883916437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1480502314371221023777165 555188367889207883916437)
                ·
                  refine ⟨26024454744806619558583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 555188367889207883916437 26024454744806619558583)
                  ·
                    rfl

theorem cell23_456142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 3, 6].length) (baseStart_456142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456142 prefixEnd_456142 := by exact prefixLift 456142
  have htrace : WordTrace (prefixWord ++ tailWord_456142) baseStart_456142 baseEnd_456142 := by
    simpa [prefixWord, tailWord_456142, baseEnd_456142] using wordTrace_append hprefix tailTrace_456142
  have hstable : (prefixWord ++ tailWord_456142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456142).length < 2 ^ (prefixWord ++ tailWord_456142).sum := by decide
  have hdescent : baseEnd_456142 < baseStart_456142 := by decide
  rcases family_descends (prefixWord ++ tailWord_456142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456186 : List Nat := [3, 1, 1, 1, 1, 2, 3, 6, 1, 1, 3]
def baseStart_456186 : Nat := 118140960795 + 456186 * 2 ^ 59
def prefixEnd_456186 : Nat := 4983230072969 + 3 ^ 40 * 456186 * 2
def baseEnd_456186 : Nat := 234242685852057403877045

theorem tailTrace_456186 : CollatzResearch.WordTrace tailWord_456186 prefixEnd_456186 234242685852057403877045 := by
  unfold tailWord_456186
  simp only [CollatzResearch.WordTrace]
  refine ⟨4159617581330876802787103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11092313550215671474098941 4159617581330876802787103)
  ·
    refine ⟨6239426371996315204180655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4159617581330876802787103 6239426371996315204180655)
    ·
      refine ⟨9359139557994472806270983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6239426371996315204180655 9359139557994472806270983)
      ·
        refine ⟨14038709336991709209406475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9359139557994472806270983 14038709336991709209406475)
        ·
          refine ⟨21058064005487563814109713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14038709336991709209406475 21058064005487563814109713)
          ·
            refine ⟨15793548004115672860582285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21058064005487563814109713 15793548004115672860582285)
            ·
              refine ⟨5922580501543377322718357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15793548004115672860582285 5922580501543377322718357)
              ·
                refine ⟨277620961009845812002423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5922580501543377322718357 277620961009845812002423)
                ·
                  refine ⟨416431441514768718003635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 277620961009845812002423 416431441514768718003635)
                  ·
                    refine ⟨624647162272153077005453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 416431441514768718003635 624647162272153077005453)
                    ·
                      refine ⟨234242685852057403877045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 624647162272153077005453 234242685852057403877045)
                      ·
                        rfl

theorem cell23_456186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 6, 1, 1, 3].length) (baseStart_456186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456186 prefixEnd_456186 := by exact prefixLift 456186
  have htrace : WordTrace (prefixWord ++ tailWord_456186) baseStart_456186 baseEnd_456186 := by
    simpa [prefixWord, tailWord_456186, baseEnd_456186] using wordTrace_append hprefix tailTrace_456186
  have hstable : (prefixWord ++ tailWord_456186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456186).length < 2 ^ (prefixWord ++ tailWord_456186).sum := by decide
  have hdescent : baseEnd_456186 < baseStart_456186 := by decide
  rcases family_descends (prefixWord ++ tailWord_456186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456206 : List Nat := [4, 1, 1, 2, 4, 1, 2, 2, 1, 5]
def baseStart_456206 : Nat := 118140960795 + 456206 * 2 ^ 59
def prefixEnd_456206 : Nat := 4983230072969 + 3 ^ 40 * 456206 * 2
def baseEnd_456206 : Nat := 78084318488382441875651

theorem tailTrace_456206 : CollatzResearch.WordTrace tailWord_456206 prefixEnd_456206 78084318488382441875651 := by
  unfold tailWord_456206
  simp only [CollatzResearch.WordTrace]
  refine ⟨2079899973156381328359559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11092799856834033751250981 2079899973156381328359559)
  ·
    refine ⟨3119849959734571992539339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2079899973156381328359559 3119849959734571992539339)
    ·
      refine ⟨4679774939601857988809009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3119849959734571992539339 4679774939601857988809009)
      ·
        refine ⟨3509831204701393491606757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4679774939601857988809009 3509831204701393491606757)
        ·
          refine ⟨658093350881511279676267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3509831204701393491606757 658093350881511279676267)
          ·
            refine ⟨987140026322266919514401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 658093350881511279676267 987140026322266919514401)
            ·
              refine ⟨740355019741700189635801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 987140026322266919514401 740355019741700189635801)
              ·
                refine ⟨555266264806275142226851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 740355019741700189635801 555266264806275142226851)
                ·
                  refine ⟨832899397209412713340277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 555266264806275142226851 832899397209412713340277)
                  ·
                    refine ⟨78084318488382441875651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 832899397209412713340277 78084318488382441875651)
                    ·
                      rfl

theorem cell23_456206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 2, 1, 5].length) (baseStart_456206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456206 prefixEnd_456206 := by exact prefixLift 456206
  have htrace : WordTrace (prefixWord ++ tailWord_456206) baseStart_456206 baseEnd_456206 := by
    simpa [prefixWord, tailWord_456206, baseEnd_456206] using wordTrace_append hprefix tailTrace_456206
  have hstable : (prefixWord ++ tailWord_456206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456206).length < 2 ^ (prefixWord ++ tailWord_456206).sum := by decide
  have hdescent : baseEnd_456206 < baseStart_456206 := by decide
  rcases family_descends (prefixWord ++ tailWord_456206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456209 : List Nat := [1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 4]
def baseStart_456209 : Nat := 118140960795 + 456209 * 2 ^ 59
def prefixEnd_456209 : Nat := 4983230072969 + 3 ^ 40 * 456209 * 2
def baseEnd_456209 : Nat := 234254495907110813889439

theorem tailTrace_456209 : CollatzResearch.WordTrace tailWord_456209 prefixEnd_456209 234254495907110813889439 := by
  unfold tailWord_456209
  simp only [CollatzResearch.WordTrace]
  refine ⟨16639309204240182139235681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11092872802826788092823787 16639309204240182139235681)
  ·
    refine ⟨12479481903180136604426761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16639309204240182139235681 12479481903180136604426761)
    ·
      refine ⟨9359611427385102453320071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12479481903180136604426761 9359611427385102453320071)
      ·
        refine ⟨14039417141077653679980107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9359611427385102453320071 14039417141077653679980107)
        ·
          refine ⟨21059125711616480519970161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14039417141077653679980107 21059125711616480519970161)
          ·
            refine ⟨15794344283712360389977621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21059125711616480519970161 15794344283712360389977621)
            ·
              refine ⟨740359888299016893280201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15794344283712360389977621 740359888299016893280201)
              ·
                refine ⟨555269916224262669960151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 740359888299016893280201 555269916224262669960151)
                ·
                  refine ⟨832904874336394004940227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 555269916224262669960151 832904874336394004940227)
                  ·
                    refine ⟨1249357311504591007410341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 832904874336394004940227 1249357311504591007410341)
                    ·
                      refine ⟨234254495907110813889439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1249357311504591007410341 234254495907110813889439)
                      ·
                        rfl

theorem cell23_456209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 4].length) (baseStart_456209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456209 prefixEnd_456209 := by exact prefixLift 456209
  have htrace : WordTrace (prefixWord ++ tailWord_456209) baseStart_456209 baseEnd_456209 := by
    simpa [prefixWord, tailWord_456209, baseEnd_456209] using wordTrace_append hprefix tailTrace_456209
  have hstable : (prefixWord ++ tailWord_456209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456209).length < 2 ^ (prefixWord ++ tailWord_456209).sum := by decide
  have hdescent : baseEnd_456209 < baseStart_456209 := by decide
  rcases family_descends (prefixWord ++ tailWord_456209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456226 : List Nat := [3, 3, 1, 1, 1, 1, 2, 2, 5, 2, 2]
def baseStart_456226 : Nat := 118140960795 + 456226 * 2 ^ 59
def prefixEnd_456226 : Nat := 4983230072969 + 3 ^ 40 * 456226 * 2
def baseEnd_456226 : Nat := 234263225078237247376861

theorem tailTrace_456226 : CollatzResearch.WordTrace tailWord_456226 prefixEnd_456226 234263225078237247376861 := by
  unfold tailWord_456226
  simp only [CollatzResearch.WordTrace]
  refine ⟨4159982311294648510651133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11093286163452396028403021 4159982311294648510651133)
  ·
    refine ⟨1559993366735493191494175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4159982311294648510651133 1559993366735493191494175)
    ·
      refine ⟨2339990050103239787241263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1559993366735493191494175 2339990050103239787241263)
      ·
        refine ⟨3509985075154859680861895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2339990050103239787241263 3509985075154859680861895)
        ·
          refine ⟨5264977612732289521292843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3509985075154859680861895 5264977612732289521292843)
          ·
            refine ⟨7897466419098434281939265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5264977612732289521292843 7897466419098434281939265)
            ·
              refine ⟨5923099814323825711454449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7897466419098434281939265 5923099814323825711454449)
              ·
                refine ⟨4442324860742869283590837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5923099814323825711454449 4442324860742869283590837)
                ·
                  refine ⟨416467955694643995336641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4442324860742869283590837 416467955694643995336641)
                  ·
                    refine ⟨312350966770982996502481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 416467955694643995336641 312350966770982996502481)
                    ·
                      refine ⟨234263225078237247376861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 312350966770982996502481 234263225078237247376861)
                      ·
                        rfl

theorem cell23_456226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 5, 2, 2].length) (baseStart_456226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456226 prefixEnd_456226 := by exact prefixLift 456226
  have htrace : WordTrace (prefixWord ++ tailWord_456226) baseStart_456226 baseEnd_456226 := by
    simpa [prefixWord, tailWord_456226, baseEnd_456226] using wordTrace_append hprefix tailTrace_456226
  have hstable : (prefixWord ++ tailWord_456226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456226).length < 2 ^ (prefixWord ++ tailWord_456226).sum := by decide
  have hdescent : baseEnd_456226 < baseStart_456226 := by decide
  rcases family_descends (prefixWord ++ tailWord_456226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456243 : List Nat := [1, 1, 1, 2, 4, 5, 1, 1, 3, 2, 2]
def baseStart_456243 : Nat := 118140960795 + 456243 * 2 ^ 59
def prefixEnd_456243 : Nat := 4983230072969 + 3 ^ 40 * 456243 * 2
def baseEnd_456243 : Nat := 234271954249363680864283

theorem tailTrace_456243 : CollatzResearch.WordTrace tailWord_456243 prefixEnd_456243 234271954249363680864283 := by
  unfold tailWord_456243
  simp only [CollatzResearch.WordTrace]
  refine ⟨16640549286117005945973383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11093699524078003963982255 16640549286117005945973383)
  ·
    refine ⟨24960823929175508918960075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16640549286117005945973383 24960823929175508918960075)
    ·
      refine ⟨37441235893763263378440113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24960823929175508918960075 37441235893763263378440113)
      ·
        refine ⟨28080926920322447533830085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37441235893763263378440113 28080926920322447533830085)
        ·
          refine ⟨5265173797560458912593141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28080926920322447533830085 5265173797560458912593141)
          ·
            refine ⟨493610043521293023055607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5265173797560458912593141 493610043521293023055607)
            ·
              refine ⟨740415065281939534583411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 493610043521293023055607 740415065281939534583411)
              ·
                refine ⟨1110622597922909301875117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 740415065281939534583411 1110622597922909301875117)
                ·
                  refine ⟨416483474221090988203169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1110622597922909301875117 416483474221090988203169)
                  ·
                    refine ⟨312362605665818241152377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 416483474221090988203169 312362605665818241152377)
                    ·
                      refine ⟨234271954249363680864283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 312362605665818241152377 234271954249363680864283)
                      ·
                        rfl

theorem cell23_456243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 3, 2, 2].length) (baseStart_456243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456243 prefixEnd_456243 := by exact prefixLift 456243
  have htrace : WordTrace (prefixWord ++ tailWord_456243) baseStart_456243 baseEnd_456243 := by
    simpa [prefixWord, tailWord_456243, baseEnd_456243] using wordTrace_append hprefix tailTrace_456243
  have hstable : (prefixWord ++ tailWord_456243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456243).length < 2 ^ (prefixWord ++ tailWord_456243).sum := by decide
  have hdescent : baseEnd_456243 < baseStart_456243 := by decide
  rcases family_descends (prefixWord ++ tailWord_456243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456263 : List Nat := [1, 1, 4, 1, 5, 2, 1, 2, 1, 2, 3]
def baseStart_456263 : Nat := 118140960795 + 456263 * 2 ^ 59
def prefixEnd_456263 : Nat := 4983230072969 + 3 ^ 40 * 456263 * 2
def baseEnd_456263 : Nat := 234282223862453602614191

theorem tailTrace_456263 : CollatzResearch.WordTrace tailWord_456263 prefixEnd_456263 234282223862453602614191 := by
  unfold tailWord_456263
  simp only [CollatzResearch.WordTrace]
  refine ⟨16641278746044549361701443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11094185830696366241134295 16641278746044549361701443)
  ·
    refine ⟨24961918119066824042552165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16641278746044549361701443 24961918119066824042552165)
    ·
      refine ⟨4680359647325029507978531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24961918119066824042552165 4680359647325029507978531)
      ·
        refine ⟨7020539470987544261967797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4680359647325029507978531 7020539470987544261967797)
        ·
          refine ⟨658175575405082274559481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7020539470987544261967797 658175575405082274559481)
          ·
            refine ⟨493631681553811705919611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 658175575405082274559481 493631681553811705919611)
            ·
              refine ⟨740447522330717558879417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 493631681553811705919611 740447522330717558879417)
              ·
                refine ⟨555335641748038169159563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 740447522330717558879417 555335641748038169159563)
                ·
                  refine ⟨833003462622057253739345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 555335641748038169159563 833003462622057253739345)
                  ·
                    refine ⟨624752596966542940304509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 833003462622057253739345 624752596966542940304509)
                    ·
                      refine ⟨234282223862453602614191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 624752596966542940304509 234282223862453602614191)
                      ·
                        rfl

theorem cell23_456263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 2, 1, 2, 3].length) (baseStart_456263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456263 prefixEnd_456263 := by exact prefixLift 456263
  have htrace : WordTrace (prefixWord ++ tailWord_456263) baseStart_456263 baseEnd_456263 := by
    simpa [prefixWord, tailWord_456263, baseEnd_456263] using wordTrace_append hprefix tailTrace_456263
  have hstable : (prefixWord ++ tailWord_456263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456263).length < 2 ^ (prefixWord ++ tailWord_456263).sum := by decide
  have hdescent : baseEnd_456263 < baseStart_456263 := by decide
  rcases family_descends (prefixWord ++ tailWord_456263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456282 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 4, 3, 4]
def baseStart_456282 : Nat := 118140960795 + 456282 * 2 ^ 59
def prefixEnd_456282 : Nat := 4983230072969 + 3 ^ 40 * 456282 * 2
def baseEnd_456282 : Nat := 234291979994889028276603

theorem tailTrace_456282 : CollatzResearch.WordTrace tailWord_456282 prefixEnd_456282 234291979994889028276603 := by
  unfold tailWord_456282
  simp only [CollatzResearch.WordTrace]
  refine ⟨4160492933243928901660775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11094647821983810404428733 4160492933243928901660775)
  ·
    refine ⟨6240739399865893352491163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4160492933243928901660775 6240739399865893352491163)
    ·
      refine ⟨9361109099798840028736745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6240739399865893352491163 9361109099798840028736745)
      ·
        refine ⟨7020831824849130021552559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9361109099798840028736745 7020831824849130021552559)
        ·
          refine ⟨10531247737273695032328839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7020831824849130021552559 10531247737273695032328839)
          ·
            refine ⟨15796871605910542548493259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10531247737273695032328839 15796871605910542548493259)
            ·
              refine ⟨23695307408865813822739889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15796871605910542548493259 23695307408865813822739889)
              ·
                refine ⟨17771480556649360367054917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23695307408865813822739889 17771480556649360367054917)
                ·
                  refine ⟨3332152604371755068822797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17771480556649360367054917 3332152604371755068822797)
                  ·
                    refine ⟨1249557226639408150808549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3332152604371755068822797 1249557226639408150808549)
                    ·
                      refine ⟨234291979994889028276603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1249557226639408150808549 234291979994889028276603)
                      ·
                        rfl

theorem cell23_456282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_456282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456282 prefixEnd_456282 := by exact prefixLift 456282
  have htrace : WordTrace (prefixWord ++ tailWord_456282) baseStart_456282 baseEnd_456282 := by
    simpa [prefixWord, tailWord_456282, baseEnd_456282] using wordTrace_append hprefix tailTrace_456282
  have hstable : (prefixWord ++ tailWord_456282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456282).length < 2 ^ (prefixWord ++ tailWord_456282).sum := by decide
  have hdescent : baseEnd_456282 < baseStart_456282 := by decide
  rcases family_descends (prefixWord ++ tailWord_456282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456293 : List Nat := [1, 3, 1, 3, 3, 2, 2, 2, 2, 1, 3]
def baseStart_456293 : Nat := 118140960795 + 456293 * 2 ^ 59
def prefixEnd_456293 : Nat := 4983230072969 + 3 ^ 40 * 456293 * 2
def baseEnd_456293 : Nat := 234297628282088485239053

theorem tailTrace_456293 : CollatzResearch.WordTrace tailWord_456293 prefixEnd_456293 234297628282088485239053 := by
  unfold tailWord_456293
  simp only [CollatzResearch.WordTrace]
  refine ⟨16642372935935864485293533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11094915290623909656862355 16642372935935864485293533)
  ·
    refine ⟨6240889850975949181985075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16642372935935864485293533 6240889850975949181985075)
    ·
      refine ⟨9361334776463923772977613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6240889850975949181985075 9361334776463923772977613)
      ·
        refine ⟨3510500541173971414866605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9361334776463923772977613 3510500541173971414866605)
        ·
          refine ⟨1316437702940239280574977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3510500541173971414866605 1316437702940239280574977)
          ·
            refine ⟨987328277205179460431233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1316437702940239280574977 987328277205179460431233)
            ·
              refine ⟨740496207903884595323425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 987328277205179460431233 740496207903884595323425)
              ·
                refine ⟨555372155927913446492569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 740496207903884595323425 555372155927913446492569)
                ·
                  refine ⟨416529116945935084869427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 555372155927913446492569 416529116945935084869427)
                  ·
                    refine ⟨624793675418902627304141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 416529116945935084869427 624793675418902627304141)
                    ·
                      refine ⟨234297628282088485239053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 624793675418902627304141 234297628282088485239053)
                      ·
                        rfl

theorem cell23_456293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_456293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456293 prefixEnd_456293 := by exact prefixLift 456293
  have htrace : WordTrace (prefixWord ++ tailWord_456293) baseStart_456293 baseEnd_456293 := by
    simpa [prefixWord, tailWord_456293, baseEnd_456293] using wordTrace_append hprefix tailTrace_456293
  have hstable : (prefixWord ++ tailWord_456293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456293).length < 2 ^ (prefixWord ++ tailWord_456293).sum := by decide
  have hdescent : baseEnd_456293 < baseStart_456293 := by decide
  rcases family_descends (prefixWord ++ tailWord_456293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456309 : List Nat := [1, 3, 4, 2, 1, 1, 1, 1, 1, 8]
def baseStart_456309 : Nat := 118140960795 + 456309 * 2 ^ 59
def prefixEnd_456309 : Nat := 4983230072969 + 3 ^ 40 * 456309 * 2
def baseEnd_456309 : Nat := 78101947990853474212993

theorem tailTrace_456309 : CollatzResearch.WordTrace tailWord_456309 prefixEnd_456309 78101947990853474212993 := by
  unfold tailWord_456309
  simp only [CollatzResearch.WordTrace]
  refine ⟨16642956503877899217875981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11095304335918599478583987 16642956503877899217875981)
  ·
    refine ⟨6241108688954212206703493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16642956503877899217875981 6241108688954212206703493)
    ·
      refine ⟨1170207879178914788756905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6241108688954212206703493 1170207879178914788756905)
      ·
        refine ⟨877655909384186091567679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1170207879178914788756905 877655909384186091567679)
        ·
          refine ⟨1316483864076279137351519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 877655909384186091567679 1316483864076279137351519)
          ·
            refine ⟨1974725796114418706027279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1316483864076279137351519 1974725796114418706027279)
            ·
              refine ⟨2962088694171628059040919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1974725796114418706027279 2962088694171628059040919)
              ·
                refine ⟨4443133041257442088561379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2962088694171628059040919 4443133041257442088561379)
                ·
                  refine ⟨6664699561886163132842069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4443133041257442088561379 6664699561886163132842069)
                  ·
                    refine ⟨78101947990853474212993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 6664699561886163132842069 78101947990853474212993)
                    ·
                      rfl

theorem cell23_456309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_456309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456309 prefixEnd_456309 := by exact prefixLift 456309
  have htrace : WordTrace (prefixWord ++ tailWord_456309) baseStart_456309 baseEnd_456309 := by
    simpa [prefixWord, tailWord_456309, baseEnd_456309] using wordTrace_append hprefix tailTrace_456309
  have hstable : (prefixWord ++ tailWord_456309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456309).length < 2 ^ (prefixWord ++ tailWord_456309).sum := by decide
  have hdescent : baseEnd_456309 < baseStart_456309 := by decide
  rcases family_descends (prefixWord ++ tailWord_456309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456316 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 6, 2, 2]
def baseStart_456316 : Nat := 118140960795 + 456316 * 2 ^ 59
def prefixEnd_456316 : Nat := 4983230072969 + 3 ^ 40 * 456316 * 2
def baseEnd_456316 : Nat := 234309438337141895251447

theorem tailTrace_456316 : CollatzResearch.WordTrace tailWord_456316 prefixEnd_456316 234309438337141895251447 := by
  unfold tailWord_456316
  simp only [CollatzResearch.WordTrace]
  refine ⟨8321605907426269706690401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11095474543235026275587201 8321605907426269706690401)
  ·
    refine ⟨6241204430569702280017801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8321605907426269706690401 6241204430569702280017801)
    ·
      refine ⟨4680903322927276710013351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6241204430569702280017801 4680903322927276710013351)
      ·
        refine ⟨7021354984390915065020027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4680903322927276710013351 7021354984390915065020027)
        ·
          refine ⟨10532032476586372597530041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7021354984390915065020027 10532032476586372597530041)
          ·
            refine ⟨7899024357439779448147531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10532032476586372597530041 7899024357439779448147531)
            ·
              refine ⟨11848536536159669172221297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7899024357439779448147531 11848536536159669172221297)
              ·
                refine ⟨8886402402119751879165973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11848536536159669172221297 8886402402119751879165973)
                ·
                  refine ⟨416550112599363369335905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8886402402119751879165973 416550112599363369335905)
                  ·
                    refine ⟨312412584449522527001929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 416550112599363369335905 312412584449522527001929)
                    ·
                      refine ⟨234309438337141895251447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 312412584449522527001929 234309438337141895251447)
                      ·
                        rfl

theorem cell23_456316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 6, 2, 2].length) (baseStart_456316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456316 prefixEnd_456316 := by exact prefixLift 456316
  have htrace : WordTrace (prefixWord ++ tailWord_456316) baseStart_456316 baseEnd_456316 := by
    simpa [prefixWord, tailWord_456316, baseEnd_456316] using wordTrace_append hprefix tailTrace_456316
  have hstable : (prefixWord ++ tailWord_456316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456316).length < 2 ^ (prefixWord ++ tailWord_456316).sum := by decide
  have hdescent : baseEnd_456316 < baseStart_456316 := by decide
  rcases family_descends (prefixWord ++ tailWord_456316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456350 : List Nat := [4, 3, 1, 1, 1, 3, 1, 1, 4, 2, 2]
def baseStart_456350 : Nat := 118140960795 + 456350 * 2 ^ 59
def prefixEnd_456350 : Nat := 4983230072969 + 3 ^ 40 * 456350 * 2
def baseEnd_456350 : Nat := 234326896679394762226291

theorem tailTrace_456350 : CollatzResearch.WordTrace tailWord_456350 prefixEnd_456350 234326896679394762226291 := by
  unfold tailWord_456350
  simp only [CollatzResearch.WordTrace]
  refine ⟨2080556487091170402514813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11096301264486242146745669 2080556487091170402514813)
  ·
    refine ⟨780208682659188900943055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2080556487091170402514813 780208682659188900943055)
    ·
      refine ⟨1170313023988783351414583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 780208682659188900943055 1170313023988783351414583)
      ·
        refine ⟨1755469535983175027121875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1170313023988783351414583 1755469535983175027121875)
        ·
          refine ⟨2633204303974762540682813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1755469535983175027121875 2633204303974762540682813)
          ·
            refine ⟨987451613990535952756055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2633204303974762540682813 987451613990535952756055)
            ·
              refine ⟨1481177420985803929134083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 987451613990535952756055 1481177420985803929134083)
              ·
                refine ⟨2221766131478705893701125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1481177420985803929134083 2221766131478705893701125)
                ·
                  refine ⟨416581149652257355068961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2221766131478705893701125 416581149652257355068961)
                  ·
                    refine ⟨312435862239193016301721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 416581149652257355068961 312435862239193016301721)
                    ·
                      refine ⟨234326896679394762226291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 312435862239193016301721 234326896679394762226291)
                      ·
                        rfl

theorem cell23_456350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_456350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456350 prefixEnd_456350 := by exact prefixLift 456350
  have htrace : WordTrace (prefixWord ++ tailWord_456350) baseStart_456350 baseEnd_456350 := by
    simpa [prefixWord, tailWord_456350, baseEnd_456350] using wordTrace_append hprefix tailTrace_456350
  have hstable : (prefixWord ++ tailWord_456350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456350).length < 2 ^ (prefixWord ++ tailWord_456350).sum := by decide
  have hdescent : baseEnd_456350 < baseStart_456350 := by decide
  rcases family_descends (prefixWord ++ tailWord_456350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456356 : List Nat := [2, 3, 1, 2, 2, 2, 2, 4, 5]
def baseStart_456356 : Nat := 118140960795 + 456356 * 2 ^ 59
def prefixEnd_456356 : Nat := 4983230072969 + 3 ^ 40 * 456356 * 2
def baseEnd_456356 : Nat := 26036664173702415416807

theorem tailTrace_456356 : CollatzResearch.WordTrace tailWord_456356 prefixEnd_456356 26036664173702415416807 := by
  unfold tailWord_456356
  simp only [CollatzResearch.WordTrace]
  refine ⟨8322335367353813122418461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11096447156471750829891281 8322335367353813122418461)
  ·
    refine ⟨3120875762757679920906923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8322335367353813122418461 3120875762757679920906923)
    ·
      refine ⟨4681313644136519881360385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3120875762757679920906923 4681313644136519881360385)
      ·
        refine ⟨3510985233102389911020289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4681313644136519881360385 3510985233102389911020289)
        ·
          refine ⟨2633238924826792433265217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3510985233102389911020289 2633238924826792433265217)
          ·
            refine ⟨1974929193620094324948913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2633238924826792433265217 1974929193620094324948913)
            ·
              refine ⟨1481196895215070743711685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1974929193620094324948913 1481196895215070743711685)
              ·
                refine ⟨277724417852825764445941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1481196895215070743711685 277724417852825764445941)
                ·
                  refine ⟨26036664173702415416807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 277724417852825764445941 26036664173702415416807)
                  ·
                    rfl

theorem cell23_456356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 4, 5].length) (baseStart_456356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456356 prefixEnd_456356 := by exact prefixLift 456356
  have htrace : WordTrace (prefixWord ++ tailWord_456356) baseStart_456356 baseEnd_456356 := by
    simpa [prefixWord, tailWord_456356, baseEnd_456356] using wordTrace_append hprefix tailTrace_456356
  have hstable : (prefixWord ++ tailWord_456356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456356).length < 2 ^ (prefixWord ++ tailWord_456356).sum := by decide
  have hdescent : baseEnd_456356 < baseStart_456356 := by decide
  rcases family_descends (prefixWord ++ tailWord_456356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456399 : List Nat := [1, 1, 2, 1, 1, 3, 1, 4, 5, 4]
def baseStart_456399 : Nat := 118140960795 + 456399 * 2 ^ 59
def prefixEnd_456399 : Nat := 4983230072969 + 3 ^ 40 * 456399 * 2
def baseEnd_456399 : Nat := 78117352410488356837855

theorem tailTrace_456399 : CollatzResearch.WordTrace tailWord_456399 prefixEnd_456399 78117352410488356837855 := by
  unfold tailWord_456399
  simp only [CollatzResearch.WordTrace]
  refine ⟨16646239073551844588652251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11097492715701229725768167 16646239073551844588652251)
  ·
    refine ⟨24969358610327766882978377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16646239073551844588652251 24969358610327766882978377)
    ·
      refine ⟨18727018957745825162233783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24969358610327766882978377 18727018957745825162233783)
      ·
        refine ⟨28090528436618737743350675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18727018957745825162233783 28090528436618737743350675)
        ·
          refine ⟨42135792654928106615026013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28090528436618737743350675 42135792654928106615026013)
          ·
            refine ⟨15800922245598039980634755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42135792654928106615026013 15800922245598039980634755)
            ·
              refine ⟨23701383368397059970952133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15800922245598039980634755 23701383368397059970952133)
              ·
                refine ⟨4444009381574448744553525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23701383368397059970952133 4444009381574448744553525)
                ·
                  refine ⟨416625879522604569801893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4444009381574448744553525 416625879522604569801893)
                  ·
                    refine ⟨78117352410488356837855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 416625879522604569801893 78117352410488356837855)
                    ·
                      rfl

theorem cell23_456399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 5, 4].length) (baseStart_456399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456399 prefixEnd_456399 := by exact prefixLift 456399
  have htrace : WordTrace (prefixWord ++ tailWord_456399) baseStart_456399 baseEnd_456399 := by
    simpa [prefixWord, tailWord_456399, baseEnd_456399] using wordTrace_append hprefix tailTrace_456399
  have hstable : (prefixWord ++ tailWord_456399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456399).length < 2 ^ (prefixWord ++ tailWord_456399).sum := by decide
  have hdescent : baseEnd_456399 < baseStart_456399 := by decide
  rcases family_descends (prefixWord ++ tailWord_456399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456413 : List Nat := [1, 4, 3, 3, 1, 1, 1, 1, 1, 2, 5]
def baseStart_456413 : Nat := 118140960795 + 456413 * 2 ^ 59
def prefixEnd_456413 : Nat := 4983230072969 + 3 ^ 40 * 456413 * 2
def baseEnd_456413 : Nat := 234359245960628015738501

theorem tailTrace_456413 : CollatzResearch.WordTrace tailWord_456413 prefixEnd_456413 234359245960628015738501 := by
  unfold tailWord_456413
  simp only [CollatzResearch.WordTrace]
  refine ⟨16646749695501124979661893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11097833130334083319774595 16646749695501124979661893)
  ·
    refine ⟨3121265567906460933686605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16646749695501124979661893 3121265567906460933686605)
    ·
      refine ⟨1170474587964922850132477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3121265567906460933686605 1170474587964922850132477)
      ·
        refine ⟨438927970486846068799679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1170474587964922850132477 438927970486846068799679)
        ·
          refine ⟨658391955730269103199519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438927970486846068799679 658391955730269103199519)
          ·
            refine ⟨987587933595403654799279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 658391955730269103199519 987587933595403654799279)
            ·
              refine ⟨1481381900393105482198919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 987587933595403654799279 1481381900393105482198919)
              ·
                refine ⟨2222072850589658223298379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1481381900393105482198919 2222072850589658223298379)
                ·
                  refine ⟨3333109275884487334947569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2222072850589658223298379 3333109275884487334947569)
                  ·
                    refine ⟨2499831956913365501210677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3333109275884487334947569 2499831956913365501210677)
                    ·
                      refine ⟨234359245960628015738501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2499831956913365501210677 234359245960628015738501)
                      ·
                        rfl

theorem cell23_456413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_456413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456413 prefixEnd_456413 := by exact prefixLift 456413
  have htrace : WordTrace (prefixWord ++ tailWord_456413) baseStart_456413 baseEnd_456413 := by
    simpa [prefixWord, tailWord_456413, baseEnd_456413] using wordTrace_append hprefix tailTrace_456413
  have hstable : (prefixWord ++ tailWord_456413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456413).length < 2 ^ (prefixWord ++ tailWord_456413).sum := by decide
  have hdescent : baseEnd_456413 < baseStart_456413 := by decide
  rcases family_descends (prefixWord ++ tailWord_456413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456416 : List Nat := [2, 1, 1, 3, 1, 2, 5, 1, 3, 4]
def baseStart_456416 : Nat := 118140960795 + 456416 * 2 ^ 59
def prefixEnd_456416 : Nat := 4983230072969 + 3 ^ 40 * 456416 * 2
def baseEnd_456416 : Nat := 78120262134197168000329

theorem tailTrace_456416 : CollatzResearch.WordTrace tailWord_456416 prefixEnd_456416 78120262134197168000329 := by
  unfold tailWord_456416
  simp only [CollatzResearch.WordTrace]
  refine ⟨8323429557245128246010551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11097906076326837661347401 8323429557245128246010551)
  ·
    refine ⟨12485144335867692369015827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8323429557245128246010551 12485144335867692369015827)
    ·
      refine ⟨18727716503801538553523741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12485144335867692369015827 18727716503801538553523741)
      ·
        refine ⟨7022893688925576957571403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18727716503801538553523741 7022893688925576957571403)
        ·
          refine ⟨10534340533388365436357105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7022893688925576957571403 10534340533388365436357105)
          ·
            refine ⟨7900755400041274077267829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10534340533388365436357105 7900755400041274077267829)
            ·
              refine ⟨740695818753869444743859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7900755400041274077267829 740695818753869444743859)
              ·
                refine ⟨1111043728130804167115789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 740695818753869444743859 1111043728130804167115789)
                ·
                  refine ⟨416641398049051562668421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1111043728130804167115789 416641398049051562668421)
                  ·
                    refine ⟨78120262134197168000329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 416641398049051562668421 78120262134197168000329)
                    ·
                      rfl

theorem cell23_456416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 3, 4].length) (baseStart_456416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456416 prefixEnd_456416 := by exact prefixLift 456416
  have htrace : WordTrace (prefixWord ++ tailWord_456416) baseStart_456416 baseEnd_456416 := by
    simpa [prefixWord, tailWord_456416, baseEnd_456416] using wordTrace_append hprefix tailTrace_456416
  have hstable : (prefixWord ++ tailWord_456416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456416).length < 2 ^ (prefixWord ++ tailWord_456416).sum := by decide
  have hdescent : baseEnd_456416 < baseStart_456416 := by decide
  rcases family_descends (prefixWord ++ tailWord_456416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456439 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 2, 5, 3]
def baseStart_456439 : Nat := 118140960795 + 456439 * 2 ^ 59
def prefixEnd_456439 : Nat := 4983230072969 + 3 ^ 40 * 456439 * 2
def baseEnd_456439 : Nat := 234372596457644914013381

theorem tailTrace_456439 : CollatzResearch.WordTrace tailWord_456439 prefixEnd_456439 234372596457644914013381 := by
  unfold tailWord_456439
  simp only [CollatzResearch.WordTrace]
  refine ⟨16647697993406931420108371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11098465328937954280072247 16647697993406931420108371)
  ·
    refine ⟨24971546990110397130162557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16647697993406931420108371 24971546990110397130162557)
    ·
      refine ⟨9364330121291398923810959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24971546990110397130162557 9364330121291398923810959)
      ·
        refine ⟨14046495181937098385716439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9364330121291398923810959 14046495181937098385716439)
        ·
          refine ⟨21069742772905647578574659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14046495181937098385716439 21069742772905647578574659)
          ·
            refine ⟨31604614159358471367861989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21069742772905647578574659 31604614159358471367861989)
            ·
              refine ⟨5925865154879713381474123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31604614159358471367861989 5925865154879713381474123)
              ·
                refine ⟨8888797732319570072211185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5925865154879713381474123 8888797732319570072211185)
                ·
                  refine ⟨6666598299239677554158389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8888797732319570072211185 6666598299239677554158389)
                  ·
                    refine ⟨624993590553719770702349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6666598299239677554158389 624993590553719770702349)
                    ·
                      refine ⟨234372596457644914013381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 624993590553719770702349 234372596457644914013381)
                      ·
                        rfl

theorem cell23_456439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 5, 3].length) (baseStart_456439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456439 prefixEnd_456439 := by exact prefixLift 456439
  have htrace : WordTrace (prefixWord ++ tailWord_456439) baseStart_456439 baseEnd_456439 := by
    simpa [prefixWord, tailWord_456439, baseEnd_456439] using wordTrace_append hprefix tailTrace_456439
  have hstable : (prefixWord ++ tailWord_456439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456439).length < 2 ^ (prefixWord ++ tailWord_456439).sum := by decide
  have hdescent : baseEnd_456439 < baseStart_456439 := by decide
  rcases family_descends (prefixWord ++ tailWord_456439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456450 : List Nat := [3, 4, 1, 1, 1, 1, 2, 5, 1, 4]
def baseStart_456450 : Nat := 118140960795 + 456450 * 2 ^ 59
def prefixEnd_456450 : Nat := 4983230072969 + 3 ^ 40 * 456450 * 2
def baseEnd_456450 : Nat := 78126081581614790325277

theorem tailTrace_456450 : CollatzResearch.WordTrace tailWord_456450 prefixEnd_456450 78126081581614790325277 := by
  unfold tailWord_456450
  simp only [CollatzResearch.WordTrace]
  refine ⟨4162024799091770074689701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11098732797578053532505869 4162024799091770074689701)
  ·
    refine ⟨780379649829706889004319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4162024799091770074689701 780379649829706889004319)
    ·
      refine ⟨1170569474744560333506479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 780379649829706889004319 1170569474744560333506479)
      ·
        refine ⟨1755854212116840500259719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1170569474744560333506479 1755854212116840500259719)
        ·
          refine ⟨2633781318175260750389579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1755854212116840500259719 2633781318175260750389579)
          ·
            refine ⟨3950671977262891125584369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2633781318175260750389579 3950671977262891125584369)
            ·
              refine ⟨2963003982947168344188277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3950671977262891125584369 2963003982947168344188277)
              ·
                refine ⟨277781623401297032267651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2963003982947168344188277 277781623401297032267651)
                ·
                  refine ⟨416672435101945548401477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 277781623401297032267651 416672435101945548401477)
                  ·
                    refine ⟨78126081581614790325277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 416672435101945548401477 78126081581614790325277)
                    ·
                      rfl

theorem cell23_456450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_456450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456450 prefixEnd_456450 := by exact prefixLift 456450
  have htrace : WordTrace (prefixWord ++ tailWord_456450) baseStart_456450 baseEnd_456450 := by
    simpa [prefixWord, tailWord_456450, baseEnd_456450] using wordTrace_append hprefix tailTrace_456450
  have hstable : (prefixWord ++ tailWord_456450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456450).length < 2 ^ (prefixWord ++ tailWord_456450).sum := by decide
  have hdescent : baseEnd_456450 < baseStart_456450 := by decide
  rcases family_descends (prefixWord ++ tailWord_456450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456500 : List Nat := [2, 5, 1, 1, 2, 2, 1, 1, 1, 5, 2]
def baseStart_456500 : Nat := 118140960795 + 456500 * 2 ^ 59
def prefixEnd_456500 : Nat := 4983230072969 + 3 ^ 40 * 456500 * 2
def baseEnd_456500 : Nat := 234403918777569175350601

theorem tailTrace_456500 : CollatzResearch.WordTrace tailWord_456500 prefixEnd_456500 234403918777569175350601 := by
  unfold tailWord_456500
  simp only [CollatzResearch.WordTrace]
  refine ⟨8324961423092969419039477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11099948564123959225385969 8324961423092969419039477)
  ·
    refine ⟨780465133414965883034951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8324961423092969419039477 780465133414965883034951)
    ·
      refine ⟨1170697700122448824552427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 780465133414965883034951 1170697700122448824552427)
      ·
        refine ⟨1756046550183673236828641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1170697700122448824552427 1756046550183673236828641)
        ·
          refine ⟨1317034912637754927621481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1756046550183673236828641 1317034912637754927621481)
          ·
            refine ⟨987776184478316195716111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1317034912637754927621481 987776184478316195716111)
            ·
              refine ⟨1481664276717474293574167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 987776184478316195716111 1481664276717474293574167)
              ·
                refine ⟨2222496415076211440361251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1481664276717474293574167 2222496415076211440361251)
                ·
                  refine ⟨3333744622614317160541877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2222496415076211440361251 3333744622614317160541877)
                  ·
                    refine ⟨312538558370092233800801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3333744622614317160541877 312538558370092233800801)
                    ·
                      refine ⟨234403918777569175350601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 312538558370092233800801 234403918777569175350601)
                      ·
                        rfl

theorem cell23_456500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_456500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456500 prefixEnd_456500 := by exact prefixLift 456500
  have htrace : WordTrace (prefixWord ++ tailWord_456500) baseStart_456500 baseEnd_456500 := by
    simpa [prefixWord, tailWord_456500, baseEnd_456500] using wordTrace_append hprefix tailTrace_456500
  have hstable : (prefixWord ++ tailWord_456500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456500).length < 2 ^ (prefixWord ++ tailWord_456500).sum := by decide
  have hdescent : baseEnd_456500 < baseStart_456500 := by decide
  rcases family_descends (prefixWord ++ tailWord_456500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456506 : List Nat := [3, 1, 1, 1, 5, 1, 2, 2, 1, 6]
def baseStart_456506 : Nat := 118140960795 + 456506 * 2 ^ 59
def prefixEnd_456506 : Nat := 4983230072969 + 3 ^ 40 * 456506 * 2
def baseEnd_456506 : Nat := 78135666553832050625191

theorem tailTrace_456506 : CollatzResearch.WordTrace tailWord_456506 prefixEnd_456506 78135666553832050625191 := by
  unfold tailWord_456506
  simp only [CollatzResearch.WordTrace]
  refine ⟨4162535421041050465699343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11100094456109467908531581 4162535421041050465699343)
  ·
    refine ⟨6243803131561575698549015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4162535421041050465699343 6243803131561575698549015)
    ·
      refine ⟨9365704697342363547823523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6243803131561575698549015 9365704697342363547823523)
      ·
        refine ⟨14048557046013545321735285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9365704697342363547823523 14048557046013545321735285)
        ·
          refine ⟨1317052223063769873912683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14048557046013545321735285 1317052223063769873912683)
          ·
            refine ⟨1975578334595654810869025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1317052223063769873912683 1975578334595654810869025)
            ·
              refine ⟨1481683750946741108151769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1975578334595654810869025 1481683750946741108151769)
              ·
                refine ⟨1111262813210055831113827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1481683750946741108151769 1111262813210055831113827)
                ·
                  refine ⟨1666894219815083746670741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1111262813210055831113827 1666894219815083746670741)
                  ·
                    refine ⟨78135666553832050625191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1666894219815083746670741 78135666553832050625191)
                    ·
                      rfl

theorem cell23_456506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 1, 6].length) (baseStart_456506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456506 prefixEnd_456506 := by exact prefixLift 456506
  have htrace : WordTrace (prefixWord ++ tailWord_456506) baseStart_456506 baseEnd_456506 := by
    simpa [prefixWord, tailWord_456506, baseEnd_456506] using wordTrace_append hprefix tailTrace_456506
  have hstable : (prefixWord ++ tailWord_456506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456506).length < 2 ^ (prefixWord ++ tailWord_456506).sum := by decide
  have hdescent : baseEnd_456506 < baseStart_456506 := by decide
  rcases family_descends (prefixWord ++ tailWord_456506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456510 : List Nat := [4, 2, 1, 2, 2, 1, 4, 1, 1, 5]
def baseStart_456510 : Nat := 118140960795 + 456510 * 2 ^ 59
def prefixEnd_456510 : Nat := 4983230072969 + 3 ^ 40 * 456510 * 2
def baseEnd_456510 : Nat := 78136351194704712075185

theorem tailTrace_456510 : CollatzResearch.WordTrace tailWord_456510 prefixEnd_456510 78136351194704712075185 := by
  unfold tailWord_456510
  simp only [CollatzResearch.WordTrace]
  refine ⟨2081285947018713818242873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11100191717433140363961989 2081285947018713818242873)
  ·
    refine ⟨1560964460264035363682155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2081285947018713818242873 1560964460264035363682155)
    ·
      refine ⟨2341446690396053045523233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1560964460264035363682155 2341446690396053045523233)
      ·
        refine ⟨1756085017797039784142425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2341446690396053045523233 1756085017797039784142425)
        ·
          refine ⟨1317063763347779838106819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1756085017797039784142425 1317063763347779838106819)
          ·
            refine ⟨1975595645021669757160229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1317063763347779838106819 1975595645021669757160229)
            ·
              refine ⟨370424183441563079467543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1975595645021669757160229 370424183441563079467543)
              ·
                refine ⟨555636275162344619201315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 370424183441563079467543 555636275162344619201315)
                ·
                  refine ⟨833454412743516928801973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 555636275162344619201315 833454412743516928801973)
                  ·
                    refine ⟨78136351194704712075185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 833454412743516928801973 78136351194704712075185)
                    ·
                      rfl

theorem cell23_456510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_456510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456510 prefixEnd_456510 := by exact prefixLift 456510
  have htrace : WordTrace (prefixWord ++ tailWord_456510) baseStart_456510 baseEnd_456510 := by
    simpa [prefixWord, tailWord_456510, baseEnd_456510] using wordTrace_append hprefix tailTrace_456510
  have hstable : (prefixWord ++ tailWord_456510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456510).length < 2 ^ (prefixWord ++ tailWord_456510).sum := by decide
  have hdescent : baseEnd_456510 < baseStart_456510 := by decide
  rcases family_descends (prefixWord ++ tailWord_456510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456530 : List Nat := [3, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2]
def baseStart_456530 : Nat := 118140960795 + 456530 * 2 ^ 59
def prefixEnd_456530 : Nat := 4983230072969 + 3 ^ 40 * 456530 * 2
def baseEnd_456530 : Nat := 234419323197204057975463

theorem tailTrace_456530 : CollatzResearch.WordTrace tailWord_456530 prefixEnd_456530 234419323197204057975463 := by
  unfold tailWord_456530
  simp only [CollatzResearch.WordTrace]
  refine ⟨4162754259019313490417761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11100678024051502641114029 4162754259019313490417761)
  ·
    refine ⟨3122065694264485117813321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4162754259019313490417761 3122065694264485117813321)
    ·
      refine ⟨2341549270698363838359991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3122065694264485117813321 2341549270698363838359991)
      ·
        refine ⟨3512323906047545757539987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2341549270698363838359991 3512323906047545757539987)
        ·
          refine ⟨5268485859071318636309981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3512323906047545757539987 5268485859071318636309981)
          ·
            refine ⟨1975682197151744488616243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5268485859071318636309981 1975682197151744488616243)
            ·
              refine ⟨2963523295727616732924365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1975682197151744488616243 2963523295727616732924365)
              ·
                refine ⟨1111321235897856274846637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2963523295727616732924365 1111321235897856274846637)
                ·
                  refine ⟨416745463461696103067489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1111321235897856274846637 416745463461696103067489)
                  ·
                    refine ⟨312559097596272077300617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 416745463461696103067489 312559097596272077300617)
                    ·
                      refine ⟨234419323197204057975463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 312559097596272077300617 234419323197204057975463)
                      ·
                        rfl

theorem cell23_456530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2].length) (baseStart_456530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456530 prefixEnd_456530 := by exact prefixLift 456530
  have htrace : WordTrace (prefixWord ++ tailWord_456530) baseStart_456530 baseEnd_456530 := by
    simpa [prefixWord, tailWord_456530, baseEnd_456530] using wordTrace_append hprefix tailTrace_456530
  have hstable : (prefixWord ++ tailWord_456530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456530).length < 2 ^ (prefixWord ++ tailWord_456530).sum := by decide
  have hdescent : baseEnd_456530 < baseStart_456530 := by decide
  rcases family_descends (prefixWord ++ tailWord_456530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456540 : List Nat := [2, 2, 4, 2, 2, 2, 1, 1, 1, 6]
def baseStart_456540 : Nat := 118140960795 + 456540 * 2 ^ 59
def prefixEnd_456540 : Nat := 4983230072969 + 3 ^ 40 * 456540 * 2
def baseEnd_456540 : Nat := 78141486001249672950139

theorem tailTrace_456540 : CollatzResearch.WordTrace tailWord_456540 prefixEnd_456540 78141486001249672950139 := by
  unfold tailWord_456540
  simp only [CollatzResearch.WordTrace]
  refine ⟨8325690883020512834767537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11100921177360683779690049 8325690883020512834767537)
  ·
    refine ⟨6244268162265384626075653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8325690883020512834767537 6244268162265384626075653)
    ·
      refine ⟨1170800280424759617389185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6244268162265384626075653 1170800280424759617389185)
      ·
        refine ⟨878100210318569713041889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1170800280424759617389185 878100210318569713041889)
        ·
          refine ⟨658575157738927284781417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 878100210318569713041889 658575157738927284781417)
          ·
            refine ⟨493931368304195463586063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 658575157738927284781417 493931368304195463586063)
            ·
              refine ⟨740897052456293195379095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 493931368304195463586063 740897052456293195379095)
              ·
                refine ⟨1111345578684439793068643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 740897052456293195379095 1111345578684439793068643)
                ·
                  refine ⟨1667018368026659689602965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1111345578684439793068643 1667018368026659689602965)
                  ·
                    refine ⟨78141486001249672950139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1667018368026659689602965 78141486001249672950139)
                    ·
                      rfl

theorem cell23_456540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_456540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456540 prefixEnd_456540 := by exact prefixLift 456540
  have htrace : WordTrace (prefixWord ++ tailWord_456540) baseStart_456540 baseEnd_456540 := by
    simpa [prefixWord, tailWord_456540, baseEnd_456540] using wordTrace_append hprefix tailTrace_456540
  have hstable : (prefixWord ++ tailWord_456540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456540).length < 2 ^ (prefixWord ++ tailWord_456540).sum := by decide
  have hdescent : baseEnd_456540 < baseStart_456540 := by decide
  rcases family_descends (prefixWord ++ tailWord_456540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456543 : List Nat := [1, 1, 2, 3, 1, 6, 1, 1, 1, 2, 4]
def baseStart_456543 : Nat := 118140960795 + 456543 * 2 ^ 59
def prefixEnd_456543 : Nat := 4983230072969 + 3 ^ 40 * 456543 * 2
def baseEnd_456543 : Nat := 234425998445712507112903

theorem tailTrace_456543 : CollatzResearch.WordTrace tailWord_456543 prefixEnd_456543 234425998445712507112903 := by
  unfold tailWord_456543
  simp only [CollatzResearch.WordTrace]
  refine ⟨16651491185030157181894283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11100994123353438121262855 16651491185030157181894283)
  ·
    refine ⟨24977236777545235772841425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16651491185030157181894283 24977236777545235772841425)
    ·
      refine ⟨18732927583158926829631069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24977236777545235772841425 18732927583158926829631069)
      ·
        refine ⟨7024847843684597561111651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18732927583158926829631069 7024847843684597561111651)
        ·
          refine ⟨10537271765526896341667477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7024847843684597561111651 10537271765526896341667477)
          ·
            refine ⟨493934614009073266015663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10537271765526896341667477 493934614009073266015663)
            ·
              refine ⟨740901921013609899023495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 493934614009073266015663 740901921013609899023495)
              ·
                refine ⟨1111352881520414848535243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 740901921013609899023495 1111352881520414848535243)
                ·
                  refine ⟨1667029322280622272802865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1111352881520414848535243 1667029322280622272802865)
                  ·
                    refine ⟨1250271991710466704602149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1667029322280622272802865 1250271991710466704602149)
                    ·
                      refine ⟨234425998445712507112903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1250271991710466704602149 234425998445712507112903)
                      ·
                        rfl

theorem cell23_456543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 2, 4].length) (baseStart_456543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456543 prefixEnd_456543 := by exact prefixLift 456543
  have htrace : WordTrace (prefixWord ++ tailWord_456543) baseStart_456543 baseEnd_456543 := by
    simpa [prefixWord, tailWord_456543, baseEnd_456543] using wordTrace_append hprefix tailTrace_456543
  have hstable : (prefixWord ++ tailWord_456543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456543).length < 2 ^ (prefixWord ++ tailWord_456543).sum := by decide
  have hdescent : baseEnd_456543 < baseStart_456543 := by decide
  rcases family_descends (prefixWord ++ tailWord_456543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456573 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 5, 3, 2]
def baseStart_456573 : Nat := 118140960795 + 456573 * 2 ^ 59
def prefixEnd_456573 : Nat := 4983230072969 + 3 ^ 40 * 456573 * 2
def baseEnd_456573 : Nat := 234441402865347389737765

theorem tailTrace_456573 : CollatzResearch.WordTrace tailWord_456573 prefixEnd_456573 234441402865347389737765 := by
  unfold tailWord_456573
  simp only [CollatzResearch.WordTrace]
  refine ⟨16652585374921472305486373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11101723583280981536990915 16652585374921472305486373)
  ·
    refine ⟨3122359757797776057278695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16652585374921472305486373 3122359757797776057278695)
    ·
      refine ⟨4683539636696664085918043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3122359757797776057278695 4683539636696664085918043)
      ·
        refine ⟨7025309455044996128877065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4683539636696664085918043 7025309455044996128877065)
        ·
          refine ⟨5268982091283747096657799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7025309455044996128877065 5268982091283747096657799)
          ·
            refine ⟨7903473136925620644986699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5268982091283747096657799 7903473136925620644986699)
            ·
              refine ⟨11855209705388430967480049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7903473136925620644986699 11855209705388430967480049)
              ·
                refine ⟨8891407279041323225610037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11855209705388430967480049 8891407279041323225610037)
                ·
                  refine ⟨833569432410124052400941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8891407279041323225610037 833569432410124052400941)
                  ·
                    refine ⟨312588537153796519650353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 833569432410124052400941 312588537153796519650353)
                    ·
                      refine ⟨234441402865347389737765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 312588537153796519650353 234441402865347389737765)
                      ·
                        rfl

theorem cell23_456573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 5, 3, 2].length) (baseStart_456573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456573 prefixEnd_456573 := by exact prefixLift 456573
  have htrace : WordTrace (prefixWord ++ tailWord_456573) baseStart_456573 baseEnd_456573 := by
    simpa [prefixWord, tailWord_456573, baseEnd_456573] using wordTrace_append hprefix tailTrace_456573
  have hstable : (prefixWord ++ tailWord_456573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456573).length < 2 ^ (prefixWord ++ tailWord_456573).sum := by decide
  have hdescent : baseEnd_456573 < baseStart_456573 := by decide
  rcases family_descends (prefixWord ++ tailWord_456573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456637 : List Nat := [1, 4, 1, 2, 3, 1, 1, 4, 2, 2, 2]
def baseStart_456637 : Nat := 118140960795 + 456637 * 2 ^ 59
def prefixEnd_456637 : Nat := 4983230072969 + 3 ^ 40 * 456637 * 2
def baseEnd_456637 : Nat := 234474265627235139337471

theorem tailTrace_456637 : CollatzResearch.WordTrace tailWord_456637 prefixEnd_456637 234474265627235139337471 := by
  unfold tailWord_456637
  simp only [CollatzResearch.WordTrace]
  refine ⟨16654919646689611235816165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11103279764459740823877443 16654919646689611235816165)
  ·
    refine ⟨3122797433754302106715531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16654919646689611235816165 3122797433754302106715531)
    ·
      refine ⟨4684196150631453160073297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3122797433754302106715531 4684196150631453160073297)
      ·
        refine ⟨3513147112973589870054973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4684196150631453160073297 3513147112973589870054973)
        ·
          refine ⟨1317430167365096201270615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3513147112973589870054973 1317430167365096201270615)
          ·
            refine ⟨1976145251047644301905923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1317430167365096201270615 1976145251047644301905923)
            ·
              refine ⟨2964217876571466452858885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1976145251047644301905923 2964217876571466452858885)
              ·
                refine ⟨555790851857149959911041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2964217876571466452858885 555790851857149959911041)
                ·
                  refine ⟨416843138892862469933281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 555790851857149959911041 416843138892862469933281)
                  ·
                    refine ⟨312632354169646852449961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 416843138892862469933281 312632354169646852449961)
                    ·
                      refine ⟨234474265627235139337471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 312632354169646852449961 234474265627235139337471)
                      ·
                        rfl

theorem cell23_456637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 4, 2, 2, 2].length) (baseStart_456637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456637 prefixEnd_456637 := by exact prefixLift 456637
  have htrace : WordTrace (prefixWord ++ tailWord_456637) baseStart_456637 baseEnd_456637 := by
    simpa [prefixWord, tailWord_456637, baseEnd_456637] using wordTrace_append hprefix tailTrace_456637
  have hstable : (prefixWord ++ tailWord_456637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456637).length < 2 ^ (prefixWord ++ tailWord_456637).sum := by decide
  have hdescent : baseEnd_456637 < baseStart_456637 := by decide
  rcases family_descends (prefixWord ++ tailWord_456637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456656 : List Nat := [2, 1, 1, 1, 1, 2, 4, 2, 4, 5]
def baseStart_456656 : Nat := 118140960795 + 456656 * 2 ^ 59
def prefixEnd_456656 : Nat := 4983230072969 + 3 ^ 40 * 456656 * 2
def baseEnd_456656 : Nat := 78161340586556854999961

theorem tailTrace_456656 : CollatzResearch.WordTrace tailWord_456656 prefixEnd_456656 78161340586556854999961 := by
  unfold tailWord_456656
  simp only [CollatzResearch.WordTrace]
  refine ⟨8327806316810388740378911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11103741755747184987171881 8327806316810388740378911)
  ·
    refine ⟨12491709475215583110568367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8327806316810388740378911 12491709475215583110568367)
    ·
      refine ⟨18737564212823374665852551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12491709475215583110568367 18737564212823374665852551)
      ·
        refine ⟨28106346319235061998778827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18737564212823374665852551 28106346319235061998778827)
        ·
          refine ⟨42159519478852592998168241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28106346319235061998778827 42159519478852592998168241)
          ·
            refine ⟨31619639609139444748626181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42159519478852592998168241 31619639609139444748626181)
            ·
              refine ⟨5928682426713645890367409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31619639609139444748626181 5928682426713645890367409)
              ·
                refine ⟨4446511820035234417775557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5928682426713645890367409 4446511820035234417775557)
                ·
                  refine ⟨833720966256606453332917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4446511820035234417775557 833720966256606453332917)
                  ·
                    refine ⟨78161340586556854999961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 833720966256606453332917 78161340586556854999961)
                    ·
                      rfl

theorem cell23_456656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 4, 5].length) (baseStart_456656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456656 prefixEnd_456656 := by exact prefixLift 456656
  have htrace : WordTrace (prefixWord ++ tailWord_456656) baseStart_456656 baseEnd_456656 := by
    simpa [prefixWord, tailWord_456656, baseEnd_456656] using wordTrace_append hprefix tailTrace_456656
  have hstable : (prefixWord ++ tailWord_456656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456656).length < 2 ^ (prefixWord ++ tailWord_456656).sum := by decide
  have hdescent : baseEnd_456656 < baseStart_456656 := by decide
  rcases family_descends (prefixWord ++ tailWord_456656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456663 : List Nat := [1, 1, 3, 2, 1, 1, 3, 2, 2, 5, 2]
def baseStart_456663 : Nat := 118140960795 + 456663 * 2 ^ 59
def prefixEnd_456663 : Nat := 4983230072969 + 3 ^ 40 * 456663 * 2
def baseEnd_456663 : Nat := 234487616124252037612351

theorem tailTrace_456663 : CollatzResearch.WordTrace tailWord_456663 prefixEnd_456663 234487616124252037612351 := by
  unfold tailWord_456663
  simp only [CollatzResearch.WordTrace]
  refine ⟨16655867944595417676262643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11103911963063611784175095 16655867944595417676262643)
  ·
    refine ⟨24983801916893126514393965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16655867944595417676262643 24983801916893126514393965)
    ·
      refine ⟨9368925718834922442897737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24983801916893126514393965 9368925718834922442897737)
      ·
        refine ⟨7026694289126191832173303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9368925718834922442897737 7026694289126191832173303)
        ·
          refine ⟨10540041433689287748259955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7026694289126191832173303 10540041433689287748259955)
          ·
            refine ⟨15810062150533931622389933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10540041433689287748259955 15810062150533931622389933)
            ·
              refine ⟨5928773306450224358396225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15810062150533931622389933 5928773306450224358396225)
              ·
                refine ⟨4446579979837668268797169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5928773306450224358396225 4446579979837668268797169)
                ·
                  refine ⟨3334934984878251201597877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4446579979837668268797169 3334934984878251201597877)
                  ·
                    refine ⟨312650154832336050149801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3334934984878251201597877 312650154832336050149801)
                    ·
                      refine ⟨234487616124252037612351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 312650154832336050149801 234487616124252037612351)
                      ·
                        rfl

theorem cell23_456663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 5, 2].length) (baseStart_456663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456663 prefixEnd_456663 := by exact prefixLift 456663
  have htrace : WordTrace (prefixWord ++ tailWord_456663) baseStart_456663 baseEnd_456663 := by
    simpa [prefixWord, tailWord_456663, baseEnd_456663] using wordTrace_append hprefix tailTrace_456663
  have hstable : (prefixWord ++ tailWord_456663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456663).length < 2 ^ (prefixWord ++ tailWord_456663).sum := by decide
  have hdescent : baseEnd_456663 < baseStart_456663 := by decide
  rcases family_descends (prefixWord ++ tailWord_456663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456673 : List Nat := [1, 2, 3, 1, 2, 1, 5, 1, 2, 5]
def baseStart_456673 : Nat := 118140960795 + 456673 * 2 ^ 59
def prefixEnd_456673 : Nat := 4983230072969 + 3 ^ 40 * 456673 * 2
def baseEnd_456673 : Nat := 78164250310265666162435

theorem tailTrace_456673 : CollatzResearch.WordTrace tailWord_456673 prefixEnd_456673 78164250310265666162435 := by
  unfold tailWord_456673
  simp only [CollatzResearch.WordTrace]
  refine ⟨16656232674559189384126673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11104155116372792922751115 16656232674559189384126673)
  ·
    refine ⟨12492174505919392038095005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16656232674559189384126673 12492174505919392038095005)
    ·
      refine ⟨4684565439719772014285627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12492174505919392038095005 4684565439719772014285627)
      ·
        refine ⟨7026848159579658021428441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4684565439719772014285627 7026848159579658021428441)
        ·
          refine ⟨5270136119684743516071331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7026848159579658021428441 5270136119684743516071331)
          ·
            refine ⟨7905204179527115274106997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5270136119684743516071331 7905204179527115274106997)
            ·
              refine ⟨741112891830667056947531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7905204179527115274106997 741112891830667056947531)
              ·
                refine ⟨1111669337746000585421297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 741112891830667056947531 1111669337746000585421297)
                ·
                  refine ⟨833752003309500439065973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1111669337746000585421297 833752003309500439065973)
                  ·
                    refine ⟨78164250310265666162435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 833752003309500439065973 78164250310265666162435)
                    ·
                      rfl

theorem cell23_456673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 2, 5].length) (baseStart_456673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456673 prefixEnd_456673 := by exact prefixLift 456673
  have htrace : WordTrace (prefixWord ++ tailWord_456673) baseStart_456673 baseEnd_456673 := by
    simpa [prefixWord, tailWord_456673, baseEnd_456673] using wordTrace_append hprefix tailTrace_456673
  have hstable : (prefixWord ++ tailWord_456673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456673).length < 2 ^ (prefixWord ++ tailWord_456673).sum := by decide
  have hdescent : baseEnd_456673 < baseStart_456673 := by decide
  rcases family_descends (prefixWord ++ tailWord_456673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456696 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 2, 3, 5]
def baseStart_456696 : Nat := 118140960795 + 456696 * 2 ^ 59
def prefixEnd_456696 : Nat := 4983230072969 + 3 ^ 40 * 456696 * 2
def baseEnd_456696 : Nat := 234504560985850408499699

theorem tailTrace_456696 : CollatzResearch.WordTrace tailWord_456696 prefixEnd_456696 234504560985850408499699 := by
  unfold tailWord_456696
  simp only [CollatzResearch.WordTrace]
  refine ⟨8328535776737932156106971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11104714368983909541475961 8328535776737932156106971)
  ·
    refine ⟨12492803665106898234160457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8328535776737932156106971 12492803665106898234160457)
    ·
      refine ⟨9369602748830173675620343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12492803665106898234160457 9369602748830173675620343)
      ·
        refine ⟨14054404123245260513430515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9369602748830173675620343 14054404123245260513430515)
        ·
          refine ⟨21081606184867890770145773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14054404123245260513430515 21081606184867890770145773)
          ·
            refine ⟨7905602319325459038804665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21081606184867890770145773 7905602319325459038804665)
            ·
              refine ⟨5929201739494094279103499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7905602319325459038804665 5929201739494094279103499)
              ·
                refine ⟨8893802609241141418655249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5929201739494094279103499 8893802609241141418655249)
                ·
                  refine ⟨6670351956930856063991437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8893802609241141418655249 6670351956930856063991437)
                  ·
                    refine ⟨2501381983849071023996789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6670351956930856063991437 2501381983849071023996789)
                    ·
                      refine ⟨234504560985850408499699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2501381983849071023996789 234504560985850408499699)
                      ·
                        rfl

theorem cell23_456696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_456696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456696 prefixEnd_456696 := by exact prefixLift 456696
  have htrace : WordTrace (prefixWord ++ tailWord_456696) baseStart_456696 baseEnd_456696 := by
    simpa [prefixWord, tailWord_456696, baseEnd_456696] using wordTrace_append hprefix tailTrace_456696
  have hstable : (prefixWord ++ tailWord_456696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456696).length < 2 ^ (prefixWord ++ tailWord_456696).sum := by decide
  have hdescent : baseEnd_456696 < baseStart_456696 := by decide
  rcases family_descends (prefixWord ++ tailWord_456696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456733 : List Nat := [1, 4, 2, 2, 2, 1, 1, 2, 8]
def baseStart_456733 : Nat := 118140960795 + 456733 * 2 ^ 59
def prefixEnd_456733 : Nat := 4983230072969 + 3 ^ 40 * 456733 * 2
def baseEnd_456733 : Nat := 26058173307785195970781

theorem tailTrace_456733 : CollatzResearch.WordTrace tailWord_456733 prefixEnd_456733 26058173307785195970781 := by
  unfold tailWord_456733
  simp only [CollatzResearch.WordTrace]
  refine ⟨16658421054341819631310853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11105614036227879754207235 16658421054341819631310853)
  ·
    refine ⟨3123453947689091180870785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16658421054341819631310853 3123453947689091180870785)
    ·
      refine ⟨2342590460766818385653089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3123453947689091180870785 2342590460766818385653089)
      ·
        refine ⟨1756942845575113789239817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2342590460766818385653089 1756942845575113789239817)
        ·
          refine ⟨1317707134181335341929863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1756942845575113789239817 1317707134181335341929863)
          ·
            refine ⟨1976560701272003012894795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1317707134181335341929863 1976560701272003012894795)
            ·
              refine ⟨2964841051908004519342193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1976560701272003012894795 2964841051908004519342193)
              ·
                refine ⟨2223630788931003389506645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2964841051908004519342193 2223630788931003389506645)
                ·
                  refine ⟨26058173307785195970781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2223630788931003389506645 26058173307785195970781)
                  ·
                    rfl

theorem cell23_456733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 8].length) (baseStart_456733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456733 prefixEnd_456733 := by exact prefixLift 456733
  have htrace : WordTrace (prefixWord ++ tailWord_456733) baseStart_456733 baseEnd_456733 := by
    simpa [prefixWord, tailWord_456733, baseEnd_456733] using wordTrace_append hprefix tailTrace_456733
  have hstable : (prefixWord ++ tailWord_456733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456733).length < 2 ^ (prefixWord ++ tailWord_456733).sum := by decide
  have hdescent : baseEnd_456733 < baseStart_456733 := by decide
  rcases family_descends (prefixWord ++ tailWord_456733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456754 : List Nat := [3, 2, 1, 1, 2, 4, 3, 2, 1, 4]
def baseStart_456754 : Nat := 118140960795 + 456754 * 2 ^ 59
def prefixEnd_456754 : Nat := 4983230072969 + 3 ^ 40 * 456754 * 2
def baseEnd_456754 : Nat := 78178114287937060524811

theorem tailTrace_456754 : CollatzResearch.WordTrace tailWord_456754 prefixEnd_456754 78178114287937060524811 := by
  unfold tailWord_456754
  simp only [CollatzResearch.WordTrace]
  refine ⟨4164796746816435054456329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11106124658177160145216877 4164796746816435054456329)
  ·
    refine ⟨3123597560112326290842247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4164796746816435054456329 3123597560112326290842247)
    ·
      refine ⟨4685396340168489436263371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3123597560112326290842247 4685396340168489436263371)
      ·
        refine ⟨7028094510252734154395057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4685396340168489436263371 7028094510252734154395057)
        ·
          refine ⟨5271070882689550615796293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7028094510252734154395057 5271070882689550615796293)
          ·
            refine ⟨988325790504290740461805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5271070882689550615796293 988325790504290740461805)
            ·
              refine ⟨370622171439109027673177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 988325790504290740461805 370622171439109027673177)
              ·
                refine ⟨277966628579331770754883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 370622171439109027673177 277966628579331770754883)
                ·
                  refine ⟨416949942868997656132325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 277966628579331770754883 416949942868997656132325)
                  ·
                    refine ⟨78178114287937060524811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 416949942868997656132325 78178114287937060524811)
                    ·
                      rfl

theorem cell23_456754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 2, 1, 4].length) (baseStart_456754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456754 prefixEnd_456754 := by exact prefixLift 456754
  have htrace : WordTrace (prefixWord ++ tailWord_456754) baseStart_456754 baseEnd_456754 := by
    simpa [prefixWord, tailWord_456754, baseEnd_456754] using wordTrace_append hprefix tailTrace_456754
  have hstable : (prefixWord ++ tailWord_456754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456754).length < 2 ^ (prefixWord ++ tailWord_456754).sum := by decide
  have hdescent : baseEnd_456754 < baseStart_456754 := by decide
  rcases family_descends (prefixWord ++ tailWord_456754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456780 : List Nat := [2, 2, 1, 3, 1, 1, 5, 2, 1, 5]
def baseStart_456780 : Nat := 118140960795 + 456780 * 2 ^ 59
def prefixEnd_456780 : Nat := 4983230072969 + 3 ^ 40 * 456780 * 2
def baseEnd_456780 : Nat := 78182564453609359949771

theorem tailTrace_456780 : CollatzResearch.WordTrace tailWord_456780 prefixEnd_456780 78182564453609359949771 := by
  unfold tailWord_456780
  simp only [CollatzResearch.WordTrace]
  refine ⟨8330067642585773329135897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11106756856781031105514529 8330067642585773329135897)
  ·
    refine ⟨6247550731939329996851923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8330067642585773329135897 6247550731939329996851923)
    ·
      refine ⟨9371326097908994995277885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6247550731939329996851923 9371326097908994995277885)
      ·
        refine ⟨3514247286715873123229207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9371326097908994995277885 3514247286715873123229207)
        ·
          refine ⟨5271370930073809684843811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3514247286715873123229207 5271370930073809684843811)
          ·
            refine ⟨7907056395110714527265717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5271370930073809684843811 7907056395110714527265717)
            ·
              refine ⟨741286537041629486931161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7907056395110714527265717 741286537041629486931161)
              ·
                refine ⟨555964902781222115198371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 741286537041629486931161 555964902781222115198371)
                ·
                  refine ⟨833947354171833172797557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 555964902781222115198371 833947354171833172797557)
                  ·
                    refine ⟨78182564453609359949771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 833947354171833172797557 78182564453609359949771)
                    ·
                      rfl

theorem cell23_456780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 2, 1, 5].length) (baseStart_456780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456780 prefixEnd_456780 := by exact prefixLift 456780
  have htrace : WordTrace (prefixWord ++ tailWord_456780) baseStart_456780 baseEnd_456780 := by
    simpa [prefixWord, tailWord_456780, baseEnd_456780] using wordTrace_append hprefix tailTrace_456780
  have hstable : (prefixWord ++ tailWord_456780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456780).length < 2 ^ (prefixWord ++ tailWord_456780).sum := by decide
  have hdescent : baseEnd_456780 < baseStart_456780 := by decide
  rcases family_descends (prefixWord ++ tailWord_456780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456783 : List Nat := [1, 1, 2, 1, 1, 2, 2, 5, 3, 1, 4]
def baseStart_456783 : Nat := 118140960795 + 456783 * 2 ^ 59
def prefixEnd_456783 : Nat := 4983230072969 + 3 ^ 40 * 456783 * 2
def baseEnd_456783 : Nat := 234549233802791568111799

theorem tailTrace_456783 : CollatzResearch.WordTrace tailWord_456783 prefixEnd_456783 234549233802791568111799 := by
  unfold tailWord_456783
  simp only [CollatzResearch.WordTrace]
  refine ⟨16660244704160678170631003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11106829802773785447087335 16660244704160678170631003)
  ·
    refine ⟨24990367056241017255946505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16660244704160678170631003 24990367056241017255946505)
    ·
      refine ⟨18742775292180762941959879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24990367056241017255946505 18742775292180762941959879)
      ·
        refine ⟨28114162938271144412939819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18742775292180762941959879 28114162938271144412939819)
        ·
          refine ⟨42171244407406716619409729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28114162938271144412939819 42171244407406716619409729)
          ·
            refine ⟨31628433305555037464557297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42171244407406716619409729 31628433305555037464557297)
            ·
              refine ⟨23721324979166278098417973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31628433305555037464557297 23721324979166278098417973)
              ·
                refine ⟨2223874216796838571726685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23721324979166278098417973 2223874216796838571726685)
                ·
                  refine ⟨833952831298814464397507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2223874216796838571726685 833952831298814464397507)
                  ·
                    refine ⟨1250929246948221696596261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 833952831298814464397507 1250929246948221696596261)
                    ·
                      refine ⟨234549233802791568111799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1250929246948221696596261 234549233802791568111799)
                      ·
                        rfl

theorem cell23_456783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 3, 1, 4].length) (baseStart_456783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456783 prefixEnd_456783 := by exact prefixLift 456783
  have htrace : WordTrace (prefixWord ++ tailWord_456783) baseStart_456783 baseEnd_456783 := by
    simpa [prefixWord, tailWord_456783, baseEnd_456783] using wordTrace_append hprefix tailTrace_456783
  have hstable : (prefixWord ++ tailWord_456783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456783).length < 2 ^ (prefixWord ++ tailWord_456783).sum := by decide
  have hdescent : baseEnd_456783 < baseStart_456783 := by decide
  rcases family_descends (prefixWord ++ tailWord_456783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456793 : List Nat := [1, 2, 1, 2, 2, 1, 5, 2, 1, 6]
def baseStart_456793 : Nat := 118140960795 + 456793 * 2 ^ 59
def prefixEnd_456793 : Nat := 4983230072969 + 3 ^ 40 * 456793 * 2
def baseEnd_456793 : Nat := 78184789536445509662251

theorem tailTrace_456793 : CollatzResearch.WordTrace tailWord_456793 prefixEnd_456793 78184789536445509662251 := by
  unfold tailWord_456793
  simp only [CollatzResearch.WordTrace]
  refine ⟨16660609434124449878495033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11107072956082966585663355 16660609434124449878495033)
  ·
    refine ⟨12495457075593337408871275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16660609434124449878495033 12495457075593337408871275)
    ·
      refine ⟨18743185613390006113306913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12495457075593337408871275 18743185613390006113306913)
      ·
        refine ⟨14057389210042504584980185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18743185613390006113306913 14057389210042504584980185)
        ·
          refine ⟨10543041907531878438735139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14057389210042504584980185 10543041907531878438735139)
          ·
            refine ⟨15814562861297817658102709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10543041907531878438735139 15814562861297817658102709)
            ·
              refine ⟨1482615268246670405447129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15814562861297817658102709 1482615268246670405447129)
              ·
                refine ⟨1111961451185002804085347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1482615268246670405447129 1111961451185002804085347)
                ·
                  refine ⟨1667942176777504206128021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1111961451185002804085347 1667942176777504206128021)
                  ·
                    refine ⟨78184789536445509662251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1667942176777504206128021 78184789536445509662251)
                    ·
                      rfl

theorem cell23_456793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 6].length) (baseStart_456793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456793 prefixEnd_456793 := by exact prefixLift 456793
  have htrace : WordTrace (prefixWord ++ tailWord_456793) baseStart_456793 baseEnd_456793 := by
    simpa [prefixWord, tailWord_456793, baseEnd_456793] using wordTrace_append hprefix tailTrace_456793
  have hstable : (prefixWord ++ tailWord_456793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456793).length < 2 ^ (prefixWord ++ tailWord_456793).sum := by decide
  have hdescent : baseEnd_456793 < baseStart_456793 := by decide
  rcases family_descends (prefixWord ++ tailWord_456793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456817 : List Nat := [1, 2, 2, 2, 1, 1, 4, 3, 3, 2, 2]
def baseStart_456817 : Nat := 118140960795 + 456817 * 2 ^ 59
def prefixEnd_456817 : Nat := 4983230072969 + 3 ^ 40 * 456817 * 2
def baseEnd_456817 : Nat := 234566692145044435086643

theorem tailTrace_456817 : CollatzResearch.WordTrace tailWord_456817 prefixEnd_456817 234566692145044435086643 := by
  unfold tailWord_456817
  simp only [CollatzResearch.WordTrace]
  refine ⟨16661484786037501977368705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11107656524025001318245803 16661484786037501977368705)
  ·
    refine ⟨12496113589528126483026529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16661484786037501977368705 12496113589528126483026529)
    ·
      refine ⟨9372085192146094862269897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12496113589528126483026529 9372085192146094862269897)
      ·
        refine ⟨7029063894109571146702423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9372085192146094862269897 7029063894109571146702423)
        ·
          refine ⟨10543595841164356720053635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7029063894109571146702423 10543595841164356720053635)
          ·
            refine ⟨15815393761746535080080453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10543595841164356720053635 15815393761746535080080453)
            ·
              refine ⟨2965386330327475327515085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15815393761746535080080453 2965386330327475327515085)
              ·
                refine ⟨1112019873872803247818157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2965386330327475327515085 1112019873872803247818157)
                ·
                  refine ⟨417007452702301217931809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1112019873872803247818157 417007452702301217931809)
                  ·
                    refine ⟨312755589526725913448857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 417007452702301217931809 312755589526725913448857)
                    ·
                      refine ⟨234566692145044435086643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 312755589526725913448857 234566692145044435086643)
                      ·
                        rfl

theorem cell23_456817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 3, 2, 2].length) (baseStart_456817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456817 prefixEnd_456817 := by exact prefixLift 456817
  have htrace : WordTrace (prefixWord ++ tailWord_456817) baseStart_456817 baseEnd_456817 := by
    simpa [prefixWord, tailWord_456817, baseEnd_456817] using wordTrace_append hprefix tailTrace_456817
  have hstable : (prefixWord ++ tailWord_456817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456817).length < 2 ^ (prefixWord ++ tailWord_456817).sum := by decide
  have hdescent : baseEnd_456817 < baseStart_456817 := by decide
  rcases family_descends (prefixWord ++ tailWord_456817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456823 : List Nat := [1, 1, 3, 1, 1, 5, 3, 8]
def baseStart_456823 : Nat := 118140960795 + 456823 * 2 ^ 59
def prefixEnd_456823 : Nat := 4983230072969 + 3 ^ 40 * 456823 * 2
def baseEnd_456823 : Nat := 8687769371443385615245

theorem tailTrace_456823 : CollatzResearch.WordTrace tailWord_456823 prefixEnd_456823 8687769371443385615245 := by
  unfold tailWord_456823
  simp only [CollatzResearch.WordTrace]
  refine ⟨16661703624015765002087123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11107802416010510001391415 16661703624015765002087123)
  ·
    refine ⟨24992555436023647503130685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16661703624015765002087123 24992555436023647503130685)
    ·
      refine ⟨9372208288508867813674007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24992555436023647503130685 9372208288508867813674007)
      ·
        refine ⟨14058312432763301720511011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9372208288508867813674007 14058312432763301720511011)
        ·
          refine ⟨21087468649144952580766517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14058312432763301720511011 21087468649144952580766517)
          ·
            refine ⟨1976950185857339304446861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21087468649144952580766517 1976950185857339304446861)
            ·
              refine ⟨741356319696502239167573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1976950185857339304446861 741356319696502239167573)
              ·
                refine ⟨8687769371443385615245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 741356319696502239167573 8687769371443385615245)
                ·
                  rfl

theorem cell23_456823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 8].length) (baseStart_456823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456823 prefixEnd_456823 := by exact prefixLift 456823
  have htrace : WordTrace (prefixWord ++ tailWord_456823) baseStart_456823 baseEnd_456823 := by
    simpa [prefixWord, tailWord_456823, baseEnd_456823] using wordTrace_append hprefix tailTrace_456823
  have hstable : (prefixWord ++ tailWord_456823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456823).length < 2 ^ (prefixWord ++ tailWord_456823).sum := by decide
  have hdescent : baseEnd_456823 < baseStart_456823 := by decide
  rcases family_descends (prefixWord ++ tailWord_456823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
